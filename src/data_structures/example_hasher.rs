use std::fmt::Display;

use bimap::BiHashMap;
use itertools::Itertools;

use crate::{language::Examples, synthgraph::ExampleHash};

#[derive(Clone)]
pub struct IOExampleHashing {
    pub map: BiHashMap<Examples, ExampleHash>,
}

impl Display for IOExampleHashing {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.map
            .iter()
            .try_for_each(|(k, v)| writeln!(f, "{}: {}", k, v))
    }
}

impl Default for IOExampleHashing {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a IOExampleHashing {
    type Item = (&'a Examples, &'a ExampleHash);

    type IntoIter = bimap::hash::Iter<'a, Examples, ExampleHash>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl IOExampleHashing {
    pub fn new() -> Self {
        IOExampleHashing {
            map: BiHashMap::new(),
        }
    }

    pub fn insert(&mut self, ex: &Examples) -> ExampleHash {
        assert!(!ex.is_empty());
        if let Some(x) = self.map.get_by_left(ex) {
            return *x;
        }
        let hash = ExampleHash::new(self.map.len() as u32);
        self.map.insert(ex.clone(), hash);
        hash
    }

    pub fn get_rec_hash(&mut self) -> ExampleHash {
        /*         let ex = Examples::new(Vec::new(), Vec::new());
        if let Some(x) = self.map.get_by_left(&ex) {
            return *x;
        }
        let hash = ExampleHash(self.map.len() as u32);
        self.map.insert(ex, hash); */

        ExampleHash::new(u32::MAX)
    }

    pub fn wider(&self, ex: &Examples) -> Vec<ExampleHash> {
        self.map
            .iter()
            .filter(|(k, _)| k.is_wider(ex))
            .map(|(_, v)| *v)
            .collect_vec()
    }

    pub fn narrower(&self, ex: &Examples) -> Vec<ExampleHash> {
        self.map
            .iter()
            .filter(|(k, _)| ex.is_wider(k))
            .map(|(_, v)| *v)
            .collect_vec()
    }

    pub fn get_examples(&self, hash: ExampleHash) -> &Examples {
        self.map.get_by_right(&hash).unwrap()
    }

    pub fn contains_examples(&self, e: &Examples) -> bool {
        self.map.contains_left(e)
    }

    pub fn get_examplehash(&self, e: &Examples) -> Option<ExampleHash> {
        self.map.get_by_left(e).cloned()
    }
}
