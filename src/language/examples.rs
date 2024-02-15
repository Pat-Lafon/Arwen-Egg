use std::fmt::{Debug, Display};

use itertools::Itertools;

use tracing::info;

use crate::data_structures::InverseMap;

use super::{Constant, LinearProgram, Operation, Program, TypeSystemBounds};

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct TestCase {
    pub inputs: Vec<Constant>,
    pub output: Constant,
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.inputs.iter().map(ToString::to_string).join(","),
            self.output
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Examples {
    pub positive_examples: Vec<TestCase>,
    pub negative_examples: Vec<TestCase>,
}

/// helper function
fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
    iter: Vec<TestCase>,
    cond: &LinearProgram<T>,
    predicate: P,
) -> Vec<TestCase> {
    iter.into_iter()
        .filter(|t: &TestCase| {
            let e = t.into();
            if let Ok(res) = cond.interpret(&e) {
                assert!(matches!(res, Constant::Bool(_)));
                predicate(&res)
            } else {
                info!("Had an invalid program while filtering behaviour: {cond}");
                false
            }
        })
        .collect::<Vec<TestCase>>()
}

/// helper function
fn filter_behavior_p<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
    iter: Vec<TestCase>,
    cond: &Program<T>,
    predicate: &P,
) -> Vec<TestCase> {
    iter.into_iter()
        .filter(|t: &TestCase| {
            let e = t.into();
            if let Ok(res) = cond.interpret(&e, cond, &None) {
                assert!(matches!(res, Constant::Bool(_)));
                predicate(&res)
            } else {
                info!("Had an invalid program while filtering behaviour: {cond}");
                false
            }
        })
        .collect::<Vec<TestCase>>()
}

impl Examples {
    pub fn new(mut positive_examples: Vec<TestCase>, mut negative_examples: Vec<TestCase>) -> Self {
        positive_examples.sort();
        negative_examples.sort();
        Self {
            positive_examples,
            negative_examples,
        }
    }

    pub fn len(&self) -> usize {
        self.positive_examples.len() + self.negative_examples.len()
    }

    pub fn is_empty(&self) -> bool {
        self.positive_examples.is_empty() && self.negative_examples.is_empty()
    }

    // Only checks the positive examples because the negative examples are suppose to not be reachable
    pub fn is_observably_smaller(&self) -> bool {
        self.positive_examples
            .iter()
            // Filter out all the base case examples
            .filter(|TestCase { inputs, .. }| !inputs[0].is_base_case())
            .all(|TestCase { inputs, output }| inputs[0] > *output)
    }

    pub fn is_wider(&self, other: &Examples) -> bool {
        // None of any of the negative examples are in the other set
        // And all of the other examples are within self
        self.positive_examples.len() > other.positive_examples.len() &&
        /* self.negative_examples
            .iter()
            .any(|t| !other.positive_examples.contains(t))
            && other
                .negative_examples
                .iter()
                .any(|t| !self.positive_examples.contains(t))
            &&  */other
                .positive_examples
                .iter()
                .all(|t| self.positive_examples.contains(t))
    }

    pub fn extend(&mut self, other: Examples) {
        self.positive_examples.extend(other.positive_examples);
        self.negative_examples.extend(other.negative_examples);
    }

    pub fn get_positive_examples(&self) -> &[TestCase] {
        &self.positive_examples
    }

    pub fn get_negative_examples(&self) -> &[TestCase] {
        &self.negative_examples
    }

    pub fn get_all_examples(&self) -> Vec<TestCase> {
        let mut res = self.positive_examples.clone();
        res.extend(self.negative_examples.clone());
        res
    }

    pub fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &LinearProgram<T>,
        predicate: P,
    ) -> Examples {
        let Examples {
            positive_examples,
            negative_examples,
        } = self;
        Examples::new(
            filter_behavior(positive_examples.clone(), cond, &predicate),
            filter_behavior(negative_examples.clone(), cond, &predicate),
        )
    }

    pub fn filter_behavior_p<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: &Program<T>,
        predicate: &P,
    ) -> Examples {
        let Examples {
            positive_examples,
            negative_examples,
        } = self;
        Examples::new(
            filter_behavior_p(positive_examples.clone(), cond, predicate),
            filter_behavior_p(negative_examples.clone(), cond, predicate),
        )
    }

    pub fn filter_behavior_e(&self, cond: &Examples, predicate: bool) -> Examples {
        Examples::new(
            self.positive_examples
                .clone()
                .into_iter()
                .filter(|TestCase { inputs, .. }| {
                    cond.positive_examples.iter().any(|c| {
                        if inputs == &c.inputs {
                            TryInto::<bool>::try_into(c.output.clone()).unwrap() == predicate
                        } else {
                            false
                        }
                    })
                })
                .collect(),
            self.negative_examples
                .clone()
                .into_iter()
                .filter(|TestCase { inputs, .. }| {
                    cond.positive_examples.iter().any(|c| {
                        if inputs == &c.inputs {
                            TryInto::<bool>::try_into(c.output.clone()).unwrap() == predicate
                        } else {
                            false
                        }
                    })
                })
                .collect(),
        )
    }

    /// Provide a list of examples for each argument of the operation.
    /// TODO, this may be a source of confusion... will have to wait and see
    pub fn witness_examples<T: TypeSystemBounds>(
        &self,
        o: &Operation<T>,
        inverse_map: &InverseMap<T>,
    ) -> Option<Vec<Vec<Examples>>> {
        (0..o.sig.input.len())
            .map(|idx| inverse_map.inverse_app(o, self, idx))
            .collect()
    }

    pub fn propogate_operation_examples<T: TypeSystemBounds>(
        &self,
        o: &Operation<T>,
        inverse_map: &InverseMap<T>,
    ) -> Option<Vec<Vec<Examples>>> {
        (0..o.sig.input.len())
            .map(|idx| inverse_map.inverse_app(o, self, idx))
            .collect::<Option<_>>()
            .map(|i: Vec<_>| i.into_iter().multi_cartesian_product().collect())
    }

    /// Helper for getting a set of examples for the arguments to a recursive function.
    /// Does not translate over any negative examples
    pub fn rec_compute_example_args(&self, num_args: usize) -> Vec<Examples> {
        (0..num_args)
            .map(|idx| {
                Examples::new(
                    self.positive_examples
                        .clone()
                        .into_iter()
                        .map(|mut t| {
                            t.output = t.inputs[idx].clone();
                            t
                        })
                        .collect_vec(),
                    Vec::new(),
                )
            })
            .collect()
    }

    // New examples for the inter recursive case
    pub fn rec_new_examples(&self, other: &Examples) -> Examples {
        let mut new_examples = Vec::new();
        for t in self.positive_examples.clone().into_iter() {
            if !other.positive_examples.contains(&t) {
                new_examples.push(t);
            }
        }
        Examples::new(new_examples, Vec::new())
    }

    pub fn combine(&self, other: &Examples) -> Examples {
        let mut combined = self.clone();
        combined.extend(other.clone());
        combined
    }

    pub fn is_consistent_with<F: Fn(&TestCase) -> bool>(&self, f: F) -> bool {
        self.positive_examples.iter().all(&f) && self.negative_examples.iter().all(|t| !f(t))
    }
}

impl Display for Examples {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.negative_examples.is_empty() {
            write!(
                f,
                "[{}]",
                self.positive_examples
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        } else {
            write!(
                f,
                "{{pos: [{}], neg: [{}]}}",
                self.positive_examples
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                self.negative_examples
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        }
    }
}
