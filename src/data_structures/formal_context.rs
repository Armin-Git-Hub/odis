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

#[derive(Clone)]
/// The main data structure of formal concept analysis. The incidence is given as a set of tuples, referring to the indices of the object and attribute vectors.
pub struct FormalContext<T> {
    pub objects: Vec<T>,
    pub attributes: Vec<T>,
    pub incidence: HashSet<(usize, usize)>,
    pub atomic_object_derivations: Vec<BitSet>,
    pub atomic_attribute_derivations: Vec<BitSet>,
}

impl<T> FormalContext<T> {
    fn construct(objects: Vec<T>, attributes: Vec<T>, incidence: HashSet<(usize, usize)>) -> Self {
        let mut atomic_object_derivations =
            vec![BitSet::with_capacity(attributes.len()); objects.len()];
        let mut atomic_attribute_derivations =
            vec![BitSet::with_capacity(objects.len()); attributes.len()];
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

    /// Adds a new object with its corresponding attributes to the existing FormalContext.
    pub fn add_object(&mut self, new_object: T, attributes: &BitSet) {
        self.objects.push(new_object);
        let object_index = self.objects.len() - 1;
        self.atomic_object_derivations.push(BitSet::new());

        for attribute in attributes.iter() {
            self.incidence.insert((object_index, attribute));
            self.atomic_object_derivations[object_index].insert(attribute);
            self.atomic_attribute_derivations[attribute].insert(object_index);
        }
    }

    /// Adds a new attribute with its corresponding objects to the existing FormalContext.
    pub fn add_attribute(&mut self, new_attribute: T, objects: &BitSet) {
        self.attributes.push(new_attribute);
        let attribute_index = self.attributes.len() - 1;
        self.atomic_attribute_derivations.push(BitSet::new());

        for object in objects.iter() {
            self.incidence.insert((attribute_index, object));
            self.atomic_object_derivations[object].insert(attribute_index);
            self.atomic_attribute_derivations[attribute_index].insert(object);
        }
    }

    /// Removes the object at the specified index from the existing FormalContext.
    pub fn remove_object(&mut self, index: usize) {
        for n in 0..self.attributes.len() {
            self.incidence.remove(&(index, n));
        }

        self.incidence = self
            .incidence
            .iter()
            .map(|x| if x.0 > index { (x.0 - 1, x.1) } else { *x })
            .collect();

        for n in 0..self.attributes.len() {
            self.atomic_attribute_derivations[n].remove(index);
        }

        for n in 0..self.attributes.len() {
            self.atomic_attribute_derivations[n] = self.atomic_attribute_derivations[n]
                .iter()
                .map(|x| if x > index { x - 1 } else { x })
                .collect();
        }

        self.atomic_object_derivations.remove(index);
        self.objects.remove(index);
    }

    /// Removes the attribute at the specified index from the existing FormalContext.
    pub fn remove_attribute(&mut self, index: usize) {
        for n in 0..self.objects.len() {
            self.incidence.remove(&(n, index));
        }

        self.incidence = self
            .incidence
            .iter()
            .map(|x| if x.1 > index { (x.0, x.1 - 1) } else { *x })
            .collect();

        for n in 0..self.objects.len() {
            self.atomic_object_derivations[n].remove(index);
        }

        for n in 0..self.objects.len() {
            self.atomic_object_derivations[n] = self.atomic_object_derivations[n]
                .iter()
                .map(|x| if x > index { x - 1 } else { x })
                .collect();
        }

        self.atomic_attribute_derivations.remove(index);
        self.attributes.remove(index);
    }

    /// Changes the name of a object at the specified index to the given name.
    pub fn change_object_name(&mut self, name: T, index: usize) {
        self.objects[index] = name;
    }

    /// Changes the name of a attribute at the specified index to the given name.
    pub fn change_attribute_name(&mut self, name: T, index: usize) {
        self.attributes[index] = name;
    }

    /// In place sorts the concepts in lectic order.
    pub fn sort_lectic_order(&self, concepts: &mut [(BitSet, BitSet)]) {
        let lenght = self.attributes.len();
        let weight: Vec<usize> = (1..(lenght + 1)).map(|x| 2_usize.pow(x as u32)).collect();

        let mut order: Vec<(usize, usize)> = Vec::new();

        for (index, (_, set)) in concepts.iter().enumerate() {
            let mut sum = 0;
            for n in set {
                sum += weight[lenght - 1 - n]
            }
            order.push((index, sum));
        }

        order.sort_by(|x, y| x.1.cmp(&y.1));

        for index in 0..(order.len() - 1) {
            let swap = order[index].0;
            if index != swap {
                concepts.swap(index, swap);
                let correction = order.iter().position(|x| x.0 == index).unwrap();
                order[index] = (0, 0);
                order[correction] = (swap, 0);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::FormalContext;
    use bit_set::BitSet;
    use itertools::Itertools;
    use std::fs;

    #[test]
    fn test_read_context() {
        let context =
            FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();
        assert_eq!(context.objects.len(), 48);
        assert_eq!(context.objects[0], "Albanien");
        assert_eq!(context.objects[47], "Zypern");
        assert_eq!(context.attributes.len(), 7);
        assert_eq!(context.attributes[0], "EU");
        assert_eq!(context.attributes[6], "Europarat");
        assert_eq!(context.incidence.len(), 201);
        assert!(!context.incidence.contains(&(1, 0)));
        assert!(context.incidence.contains(&(1, 1)));
        assert!(!context.incidence.contains(&(1, 2)));
        assert!(!context.incidence.contains(&(1, 3)));
        assert!(!context.incidence.contains(&(1, 4)));
        assert!(context.incidence.contains(&(1, 5)));
        assert!(context.incidence.contains(&(1, 6)));
    }

    #[test]
    fn text_index_derivations() {
        let context =
            FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();

        assert_eq!(context.index_attribute_derivation(&BitSet::new()).len(), 48);
        assert_eq!(context.index_object_derivation(&BitSet::new()).len(), 7);
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();
        assert_eq!(
            // [0]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b10000000])),
            // [0, 1, 2, 3, 4, 5, 6, 7]
            BitSet::from_bytes(&[0b11111111])
        );
        assert_eq!(
            // [1]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b01000000])),
            // [0, 1, 2, 4, 5]
            BitSet::from_bytes(&[0b11101100])
        );
        assert_eq!(
            // [0, 1]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b11000000])),
            // [0, 1, 2, 4, 5]
            BitSet::from_bytes(&[0b11101100])
        );
        assert_eq!(
            // [0, 1, 2, 3, 4, 5]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b11111100])),
            // []
            BitSet::from_bytes(&[0b00000000])
        );
        assert_eq!(
            // [3, 4]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b00011000])),
            // [6]
            BitSet::from_bytes(&[0b00000010])
        );
        assert_eq!(
            // [2, 6, 7]
            context.index_attribute_derivation(&BitSet::from_bytes(&[0b00100011])),
            // [2, 3]
            BitSet::from_bytes(&[0b00110000])
        );
        assert_eq!(
            // [0]
            context.index_object_derivation(&BitSet::from_bytes(&[0b10000000])),
            // [0, 1, 6]
            BitSet::from_bytes(&[0b11000010])
        );
        assert_eq!(
            // [0, 1, 2, 3]
            context.index_object_derivation(&BitSet::from_bytes(&[0b11110000])),
            // [0, 6]
            BitSet::from_bytes(&[0b10000010])
        );
    }

    #[test]
    fn text_index_hulls() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();
        assert_eq!(
            context.index_attribute_hull(&BitSet::from_bytes(&[0b00000000])),
            BitSet::from_bytes(&[0b10000000])
        );
        assert_eq!(
            context.index_object_hull(&BitSet::from_bytes(&[0b00000000])),
            BitSet::from_bytes(&[0b00000000])
        );
        assert_eq!(
            context.index_attribute_hull(&(0..context.attributes.len()).collect()),
            (0..context.attributes.len()).collect()
        );
        assert_eq!(
            context.index_object_hull(&(0..context.objects.len()).collect()),
            (0..context.objects.len()).collect()
        );
        for gs in (0..context.objects.len()).powerset() {
            let sub: BitSet = gs.into_iter().collect();
            let hull = context.index_object_hull(&sub);
            assert!(sub.is_subset(&hull));
        }
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            assert!(sub.is_subset(&hull));
        }
    }

    #[test]
    fn lectic_sort() {
        let context =
            FormalContext::<String>::from(&fs::read("test_data/copy.cxt").unwrap()).unwrap();

        let mut concepts_unsorted: Vec<(BitSet, BitSet)> = context.fcbo_index_concepts().collect();
        let concepts_sorted: Vec<(BitSet, BitSet)> = context.index_concepts().collect();

        assert!(concepts_sorted != concepts_unsorted);

        context.sort_lectic_order(&mut concepts_unsorted);

        assert!(concepts_sorted == concepts_unsorted);
    }
}
