use std::{collections::HashSet, rc::Rc};

use egg::Id;

use crate::data_structures::SynthCostFunc;

#[derive(Clone, Debug)]
pub struct SynthesisSketch {
    // Current cost of synthesized program
    cost: usize,
    // Holes to be filled
    work: Vec<SynthesisInfo>,
    visited_set: Rc<HashSet<Id>>,
}

impl SynthCostFunc for SynthesisSketch {
    fn cost(&self) -> usize {
        self.cost
    }
}

#[derive(Clone, Debug)]
pub struct SynthesisInfo {
    pub id: Id,
    pub if_depth: u8,
    pub can_synthesize_rec: bool,
}

impl SynthesisSketch {
    pub fn init(empty_hole: Id) -> Self {
        Self {
            cost: 0,
            work: vec![SynthesisInfo {
                id: empty_hole,
                if_depth: 0,
                can_synthesize_rec: false,
            }],
            visited_set: Rc::new(HashSet::new()),
        }
    }

    pub fn no_more_work(&self) -> bool {
        self.work.is_empty()
    }

    pub fn update_worklist(&mut self, mut new_work: Vec<SynthesisInfo>) -> Result<(), ()> {
        if new_work.iter().any(|id| self.visited_set.contains(&id.id)) {
            return Err(());
        }

        new_work.reverse();

        for s_info in new_work {
            if self.work.iter().any(
                |SynthesisInfo {
                     id,
                     if_depth: _can_synthesize_if,
                     can_synthesize_rec: _,
                 }| id == &s_info.id,
            ) {
                // Skip, we are already going to do this work
            } else {
                self.work.push(s_info)
            }
        }
        Ok(())
    }

    pub fn get_work(&mut self) -> SynthesisInfo {
        assert!(!self.work.is_empty());
        let info = self.work.pop().unwrap();

        let new_set = Rc::make_mut(&mut self.visited_set);
        new_set.insert(info.id);

        info
    }

    pub fn add_cost_of_widen(&mut self) {
        self.cost += 1
    }

    pub fn add_cost_of_op(&mut self, args_len: usize) {
        self.cost += args_len
    }

    pub fn add_cost_of_if(&mut self) {
        self.cost += 10
    }

    pub fn add_cost_of_rec(&mut self) {
        self.cost += 20
    }
}
