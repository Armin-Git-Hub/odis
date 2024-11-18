use std::collections::HashMap;
use bit_set::BitSet;

use crate::FormalContext;

// Based on the algorithm presented in: https://www.sciencedirect.com/science/article/abs/pii/S0020025511004804?via%3Dihub

// Enum containing the different outcomes of calling fcbo_next_concept
enum OutputType {
    // Contains a newly computed formal concept and its index position
    FormalConcept(
        // 1: touple containing one formal concept
        (BitSet, BitSet),
        // 2: the index of the inner for loop
        usize,
    ),
    // Contains a new dead end attribute set and its index position
    DeadEndAttributes(
        // 1: one new dead end attribute set
        BitSet,
        // 2: the index of the inner for loop
        usize,
    ),
    // Signals that a full node was cleared
    NodeCleared,
}
// Struct used as queue entries containing the calling context for fcbo_next_concept
struct CallingContext {
    // 1: set of input attributes
    input_attr: BitSet,
    // 2: index of the inner for loop
    inner_index: usize,
    // 3: sets of dead end attributes
    dead_end_attr: Option<HashMap<usize, BitSet>>,
}

impl CallingContext {
    // Creates a new instance of itself, the dead end attribute sets are added after the next node is cleared
    fn new(input_attr: BitSet, inner_index: usize) -> Self {
        CallingContext {
            input_attr,
            inner_index,
            dead_end_attr: None,
        }
    }
}

// New canonicity test added in paper to prevent duplicate branches
fn canonicity_test_one(
    smaller_subsets: &Vec<BitSet>,
    inner_index: usize,
    input_attributes: &BitSet,
    dead_end_attr_set: &HashMap<usize, BitSet>,
) -> bool {
    dead_end_attr_set.get(&inner_index)
    .unwrap()
    .intersection(&smaller_subsets[inner_index])
    .collect::<BitSet>()
    .is_subset(&input_attributes.intersection(&smaller_subsets[inner_index])
    .collect())
}

// Old canonicity test from paper
fn canonicity_test_two(
    smaller_subsets: &Vec<BitSet>,
    inner_index: usize,
    input_attributes: &BitSet,
    next_attributes: &BitSet,
) -> bool {
    input_attributes
    .intersection(&smaller_subsets[inner_index])
    .collect::<BitSet>()
    ==
    next_attributes
    .intersection(&smaller_subsets[inner_index])
    .collect()
}


// Calculates a single OutputType enum
// Closely follows the pseudo code from paper but leaves out the halting condition which is checked in fcbo_concepts
fn fcbo_next_concept<T>(
    context: &FormalContext<T>,
    smaller_subsets: &Vec<BitSet>,
    input_attributes: &BitSet,
    inner_index: usize,
    dead_end_attr_set: &HashMap<usize, BitSet>,
) -> OutputType{

    for j in inner_index..context.attributes.len() {

        if !input_attributes.contains(j) && canonicity_test_one(smaller_subsets,j, input_attributes, dead_end_attr_set) {
            let mut new_attr = BitSet::new();
            new_attr.insert(j);

            let next_objects= context
            .index_attribute_derivation(input_attributes)
            .intersection(&context.index_attribute_derivation(&new_attr))
            .collect();
            let next_attributes = context.index_object_derivation(&next_objects);

            if canonicity_test_two(smaller_subsets, j, input_attributes, &next_attributes) {
                return OutputType::FormalConcept((next_objects, next_attributes), j);
            } else {
                return OutputType::DeadEndAttributes(next_attributes, j);
            }
        }
    }
    return OutputType::NodeCleared;
}


// Returns an iterator which has a formal concepts as an item
// The concepts are only calculated when requested with .next() or .collect()
pub fn fcbo_concepts<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = (BitSet, BitSet)> + 'a {
    // Initializing the starting state needed for calling fcbo_next_concept 

    // Constant used throughout the function
    let attr_length = context.attributes.len();

    // Subsets needed by the canonicity tests from the paper
    let mut smaller_subsets: Vec<BitSet> = Vec::new();
    for i in 0..attr_length {
        smaller_subsets.push((0..i).collect());
    }

    // The first formal concept, usually ({"all objects"},{})
    let starting_objects = context.index_attribute_derivation(&BitSet::new());
    let mut input_attributes = context.index_object_derivation(&starting_objects);

    // Set the starting attribute of the for loop of fcbo_next_concepts to 0
    let mut inner_index = 0;

    // The first dead end attribue set initialized with empty sets to pass the first canonicity test
    let mut dead_end_attr_set = HashMap::new();
    for i in 0..attr_length {
        dead_end_attr_set.insert(i, BitSet::new());
    }

    // Queue containing calling context of fcbo_next_concept
    let mut queue: Vec<CallingContext> = Vec::new();

    // Records the number of branches that a nodes generates
    let mut branches: usize = 0;

    // Condition to print the first formal concept
    let mut first_concept = true;

    std::iter::from_fn(move || {
        // Returns the first concept and is then skipped
        if first_concept {
            first_concept = false;
            return Some((starting_objects.clone(), input_attributes.clone()));
        }
        // Loops until a new formal concept is returned by fcbo_next_concept
        loop {
            let output = fcbo_next_concept(
                context,
                &smaller_subsets,
                &input_attributes,
                inner_index,
                &dead_end_attr_set
            );

            match output {
                // 1: New concept is added to queue and the concept is returned, increments index for the next fcbo_next_concept call
                OutputType::FormalConcept(formal_concept, previous_inner_index) => {

                    // Increments the index for the next call of fcbo_next_concept
                    inner_index = previous_inner_index + 1;

                    // Checks the halting condition before adding the new concept to queue to prevent unnecessary queue entries
                    if formal_concept.1 != (0..attr_length).collect() && previous_inner_index < attr_length - 1 {
                        branches += 1;
                        queue.push(CallingContext::new(formal_concept.1.clone(), inner_index));
                    }
                    return Some(formal_concept);
                }
                // 2: Saves the new dead end attribute and increments the index for the next call of fcbo_next_concept
                OutputType::DeadEndAttributes(dead_end_attributes, previous_inner_index) => {
                    dead_end_attr_set.insert(previous_inner_index, dead_end_attributes);
                    inner_index = previous_inner_index + 1;
                }
                // 3: Finishes algorithm upon empty queue or updates calling context and inserts new dead end attribte set into queue
                OutputType::NodeCleared => {
                    if queue.len() < 1 {
                        return None;
                    }
                    // If branches were generated, the next dead end attributes are added to their queue entries
                    if branches != 0 {
                        for j in 0..queue[queue.len() - branches].inner_index {
                            dead_end_attr_set.remove(&j);
                        }
                        for i in (queue.len() - branches)..(queue.len()) {
                            queue[i].dead_end_attr = Some(dead_end_attr_set.clone());
                        }
                        branches = 0;
                    }
                    // Processes the front queue entry by updating the calling context
                    let state = queue.pop().unwrap();
                    input_attributes = state.input_attr;
                    inner_index = state.inner_index;
                    dead_end_attr_set = state.dead_end_attr.unwrap();
                }
            }
        }
    })
}


#[cfg(test)]
mod tests {
    
    use std::{collections::BTreeSet, fs};
    use bit_set::BitSet;
    use itertools::Itertools;

    use crate::{algorithms::fcbo::fcbo_concepts, FormalContext};

    #[test]
    fn test_data_1() {
        let context = FormalContext::<String>::from(&fs::read("test_data/living_beings_and_water.cxt").unwrap()).unwrap();

        let concepts: BTreeSet<_> = fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }

    #[test]
    fn test_data_2() {
        let context = FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();

        let concepts: BTreeSet<_> = fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }

    #[test]
    fn test_data_3() {
        let context = FormalContext::<String>::from(&fs::read("test_data/data_from_paper.cxt").unwrap()).unwrap();

        let concepts: BTreeSet<_> = fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }
}
