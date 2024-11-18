use std::{
    collections::HashSet,
    io::{BufRead, Error},
    num::ParseIntError,
};

use bit_set::{self, BitSet};

#[derive(Debug)]
pub enum FormatError {
    IoError(Error),
    ParseError(ParseIntError),
    InvalidFormat,
}

impl From<Error> for FormatError {
    fn from(err: Error) -> FormatError {
        FormatError::IoError(err)
    }
}

impl From<ParseIntError> for FormatError {
    fn from(err: ParseIntError) -> FormatError {
        FormatError::ParseError(err)
    }
}

/// The main data structure of formal concept analysis. The incidence is given as a set of tuples, referring to the indices of the object and attribute vectors.
pub struct FormalContext<T> {
    pub objects: Vec<T>,
    pub attributes: Vec<T>,
    pub incidence: HashSet<(usize, usize)>,
    atomic_object_derivations: Vec<BitSet>,
    atomic_attribute_derivations: Vec<BitSet>,
}

impl<T> FormalContext<T> {
    fn construct(objects: Vec<T>, attributes: Vec<T>, incidence: HashSet<(usize, usize)>) -> Self {
        let mut atomic_object_derivations = vec![BitSet::with_capacity(attributes.len()); objects.len()];
        let mut atomic_attribute_derivations = vec![BitSet::with_capacity(objects.len()); attributes.len()];
        for &(g, m) in incidence.iter() {
            atomic_object_derivations[g].insert(m);
            atomic_attribute_derivations[m].insert(g);
        }

        FormalContext {
            objects,
            attributes,
            incidence,
            atomic_object_derivations,
            atomic_attribute_derivations,
        }
    }

    /// Creates an empty formal context.
    pub fn new() -> Self {
        Self::construct(Vec::new(), Vec::new(), HashSet::new())
    }

    /// Reads a formal context in Burmeister format.
    pub fn from(contents: &[u8]) -> Result<FormalContext<String>, FormatError> {
        let mut lines = contents.lines();

        if lines.next().ok_or(FormatError::InvalidFormat)?? != "B" {
            return Err(FormatError::InvalidFormat);
        }

        lines.next().ok_or(FormatError::InvalidFormat)??;

        let object_count: usize = lines.next().ok_or(FormatError::InvalidFormat)??.parse()?;
        let attribute_count: usize = lines.next().ok_or(FormatError::InvalidFormat)??.parse()?;

        lines.next().ok_or(FormatError::InvalidFormat)??;

        let mut objects: Vec<String> = Vec::with_capacity(object_count);
        for _ in 0..object_count {
            objects.push(lines.next().ok_or(FormatError::InvalidFormat)??);
        }

        let mut attributes: Vec<String> = Vec::with_capacity(object_count);
        for _ in 0..attribute_count {
            attributes.push(lines.next().ok_or(FormatError::InvalidFormat)??);
        }

        let mut incidence: HashSet<(usize, usize)> = HashSet::new();
        for g in 0..object_count {
            let line = lines.next().ok_or(FormatError::InvalidFormat)??;
            for (m, x) in line.chars().enumerate() {
                if x == 'X' || x == 'x' {
                    incidence.insert((g, m));
                }
            }
        }

        Ok(FormalContext::construct(objects, attributes, incidence))
    }

    /// Computes the attribute derivation of a given set of indices.
    pub fn index_attribute_derivation(&self, attributes: &BitSet) -> BitSet {
        match attributes.len() {
            0 => (0..self.objects.len()).collect(),
            1 => self.atomic_attribute_derivations[attributes.iter().next().unwrap()].clone(),
            _ => {
                let mut iter = attributes.iter();
                let mut result = self.atomic_attribute_derivations[iter.next().unwrap()].clone();
                for n in iter {
                    result.intersect_with(&self.atomic_attribute_derivations[n]);
                }
                result
            }
        }
    }

    /// Computes the object derivation of a given set of indices.
    pub fn index_object_derivation(&self, objects: &BitSet) -> BitSet {
        match objects.len() {
            0 => (0..self.attributes.len()).collect(),
            1 => self.atomic_object_derivations[objects.iter().next().unwrap()].clone(),
            _ => {
                let mut iter = objects.iter();
                let mut result = self.atomic_object_derivations[iter.next().unwrap()].clone();
                for n in iter {
                    result.intersect_with(&self.atomic_object_derivations[n]);
                }
                result
            }
        }
    }

    /// Computes the attribute hull of a given set of indices.
    pub fn index_attribute_hull(&self, attributes: &BitSet) -> BitSet {
        let objects = self.index_attribute_derivation(attributes);
        self.index_object_derivation(&objects)
    }

    /// Computes the object hull of a given set of indices.
    pub fn index_object_hull(&self, objects: &BitSet) -> BitSet {
        let attributes = self.index_object_derivation(objects);
        self.index_attribute_derivation(&attributes)
    }
}

#[cfg(test)]
mod tests {

    // use std::{collections::BTreeSet, fs};

    // use itertools::Itertools;

    // use super::FormalContext;

    // #[test]
    // fn test_read_context() {
    //     let context =
    //         FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();
    //     assert_eq!(context.objects.len(), 48);
    //     assert_eq!(context.objects[0], "Albanien");
    //     assert_eq!(context.objects[47], "Zypern");

    //     assert_eq!(context.attributes.len(), 7);
    //     assert_eq!(context.attributes[0], "EU");
    //     assert_eq!(context.attributes[6], "Europarat");

    //     assert_eq!(context.incidence.len(), 201);
    //     assert!(!context.incidence.contains(&(1, 0)));
    //     assert!(context.incidence.contains(&(1, 1)));
    //     assert!(!context.incidence.contains(&(1, 2)));
    //     assert!(!context.incidence.contains(&(1, 3)));
    //     assert!(!context.incidence.contains(&(1, 4)));
    //     assert!(context.incidence.contains(&(1, 5)));
    //     assert!(context.incidence.contains(&(1, 6)));
    // }

    // #[test]
    // fn text_index_derivations() {
    //     let context =
    //         FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();
    //     // let empty_set = ;
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::new()).len(),
    //         48
    //     );
    //     assert_eq!(context.index_object_derivation(&BTreeSet::new()).len(), 7);

    //     let context = FormalContext::<String>::from(
    //         &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
    //     )
    //     .unwrap();
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([0])),
    //         BTreeSet::from([0, 1, 2, 3, 4, 5, 6, 7])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([1])),
    //         BTreeSet::from([0, 1, 2, 4, 5])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([0, 1])),
    //         BTreeSet::from([0, 1, 2, 4, 5])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([0, 1, 2, 3, 4, 5])),
    //         BTreeSet::from([])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([0, 1, 2, 3, 4, 5])),
    //         BTreeSet::from([])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([3, 4])),
    //         BTreeSet::from([6])
    //     );
    //     assert_eq!(
    //         context.index_attribute_derivation(&BTreeSet::from([2, 6, 7])),
    //         BTreeSet::from([2, 3])
    //     );

    //     assert_eq!(
    //         context.index_object_derivation(&BTreeSet::from([0])),
    //         BTreeSet::from([0, 1, 6])
    //     );
    //     assert_eq!(
    //         context.index_object_derivation(&BTreeSet::from([0, 1, 2, 3])),
    //         BTreeSet::from([0, 6])
    //     );
    // }

    // #[test]
    // fn text_index_hulls() {
    //     let context = FormalContext::<String>::from(
    //         &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
    //     )
    //     .unwrap();

    //     assert_eq!(
    //         context.index_attribute_hull(&BTreeSet::from([])),
    //         BTreeSet::from([0])
    //     );

    //     assert_eq!(
    //         context.index_object_hull(&BTreeSet::from([])),
    //         BTreeSet::from([])
    //     );

    //     assert_eq!(
    //         context.index_attribute_hull(&(0..context.attributes.len()).collect()),
    //         (0..context.attributes.len()).collect()
    //     );

    //     assert_eq!(
    //         context.index_object_hull(&(0..context.objects.len()).collect()),
    //         (0..context.objects.len()).collect()
    //     );

    //     for gs in (0..context.objects.len()).powerset() {
    //         let sub: BTreeSet<usize> = gs.into_iter().collect();
    //         let hull = context.index_object_hull(&sub);
    //         assert!(sub.is_subset(&hull));
    //     }

    //     for ms in (0..context.attributes.len()).powerset() {
    //         let sub: BTreeSet<usize> = ms.into_iter().collect();
    //         let hull = context.index_attribute_hull(&sub);
    //         assert!(sub.is_subset(&hull));
    //     }
    // }
}