use std::{
    collections::{HashMap, HashSet},
    mem::swap,
};

use itertools::Itertools;

use crate::language::{BaseType, Constant, Examples, Operation, TestCase, TypeSystemBounds};

#[derive(Debug)]
struct ConstantTracker {
    // New constants appear in the outputs of geneated testcases
    new_constants: HashMap<BaseType, HashSet<Constant>>,
    // Get migrated over from the sets of previous new constants
    old_constants: HashMap<BaseType, HashSet<Constant>>,
}

impl ConstantTracker {
    pub fn new(ex: &Examples) -> Self {
        ConstantTracker {
            new_constants: HashMap::new(),
            old_constants: ex.get_all_examples().iter().fold(
                HashMap::new(),
                |acc: HashMap<BaseType, HashSet<Constant>>, TestCase { inputs, output }| {
                    inputs
                        .iter()
                        .chain(std::iter::once(output))
                        .fold(acc, |mut acc, c| {
                            let e = acc.entry(c.into()).or_default();
                            e.insert(c.clone());
                            acc
                        })
                },
            ),
        }
    }

    pub fn add(&mut self, ty: &BaseType, c: &Constant) {
        if !self
            .old_constants
            .get(ty)
            .map(|s| s.contains(c))
            .unwrap_or(false)
        {
            self.new_constants
                .entry(ty.clone())
                .or_default()
                .insert(c.clone());
        }
    }
}

#[derive(Debug)]
pub struct InverseMap<T: TypeSystemBounds> {
    constant_tracking: ConstantTracker,
    map: HashMap<Operation<T>, Vec<TestCase>>,
}

impl<T: TypeSystemBounds> InverseMap<T> {
    pub fn empty(ex: &Examples) -> Self {
        InverseMap {
            constant_tracking: ConstantTracker::new(ex),
            map: HashMap::new(),
        }
    }

    pub fn add(&mut self, o: Operation<T>, input_args: &Vec<Constant>) -> Option<&TestCase> {
        assert!(o.sig.input.len() == input_args.len());
        let entry = self.map.entry(o.clone()).or_default();

        if let Some(idx) = entry.iter().position(|t| &t.inputs == input_args) {
            return Some(&entry[idx]);
        } else {
            o.execute(&input_args).ok().map(|output| {
                self.constant_tracking.add(&o.sig.output.into(), &output);
                let t = TestCase {
                    inputs: input_args.clone(),
                    output,
                };

                entry.push(t);
                entry.last().unwrap()
            })
        }
    }

    pub fn update_mappings_with_new_constants(&mut self) {
        let mut new_constants = HashMap::new();
        swap(
            &mut self.constant_tracking.new_constants,
            &mut new_constants,
        );

        // We want two lists of constants
        // Create a copy of new constants now in out list of old ones
        new_constants.iter().for_each(|(ty, c_set)| {
            let current_set = self
                .constant_tracking
                .old_constants
                .entry(ty.clone())
                .or_default();
            current_set.extend(c_set.iter().cloned());
        });
        // All the old ones + new ones
        let all_constants = &self.constant_tracking.old_constants;

        // And just the new ones
        let new_constants = new_constants;
        // Then we iterate though all possible type-valid combinations for each operation with atleast one new constant
        // And update the list of behaviours with the new test cases
        self.map.iter_mut().for_each(|(o, behaviour)| {
            for i in 0..o.sig.input.len() {
                let tests = o
                    .sig
                    .input
                    .iter()
                    .enumerate()
                    .map(|(idx, ty)| {
                        if idx == i {
                            new_constants
                                .get(ty.into())
                                .map(|s| s.iter())
                                .into_iter()
                                .flatten()
                        } else {
                            all_constants
                                .get(ty.into())
                                .map(|s| s.iter())
                                .into_iter()
                                .flatten()
                        }
                    })
                    .multi_cartesian_product()
                    .map(|args| args.into_iter().cloned().collect_vec());

                let new_testcases = tests.filter_map(|inputs| {
                    let output = o.execute(&inputs).ok()?;
                    Some(TestCase { inputs, output })
                });

                behaviour.extend(new_testcases);
            }
        })
    }

    /// Return a list of possible examples for a given index into the operation
    pub fn inverse_app(
        &self,
        o: &Operation<T>,
        hole: &Examples,
        idx: usize,
    ) -> Option<Vec<Examples>> {
        /* info!("Computing inverse app for {o}"); */
        // Get all the inverse semantics for the operation
        let inverse_semantics = self.map.get(o).unwrap();

        // Filter out the inverse semantics that don't match the given testcase in the example
        let t_iter = hole
            .get_positive_examples()
            .iter()
            .map(|TestCase { inputs, output }| {
                inverse_semantics
                    .iter()
                    .filter(|x| x.output == *output)
                    .map(|x| {
                        let new_inputs = inputs.clone();
                        let new_output = x.inputs.get(idx).unwrap().clone();
                        TestCase {
                            inputs: new_inputs,
                            output: new_output,
                        }
                    })
                    .collect_vec()
            });

        // If any of these didn't work out, then we don't have inverse semantics for one of the fuction arguments
        if t_iter.clone().any(|i| i.is_empty()) {
            /* info!("Inverse app is empty for {o}, {hole}"); */
            return None;
        }

        // Given a nested list of possible testcases for each part of the example, combine them all together into as many example holes as needed
        Some(
            t_iter
                .multi_cartesian_product()
                .map(|args| Examples::new(args, hole.get_negative_examples().to_vec()))
                .collect(),
        )
    }

    pub fn get_all_constants(&self) -> HashMap<BaseType, HashSet<Constant>> {
        let mut map = self.constant_tracking.old_constants.clone();

        self.constant_tracking
            .new_constants
            .iter()
            .for_each(|(b, s)| map.get_mut(dbg!(b)).unwrap().extend(s.into_iter().cloned()));

        map
    }
}
