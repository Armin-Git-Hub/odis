use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::FormalContext;

// Based on the algorithm presented in: https://www.sciencedirect.com/science/article/abs/pii/S0020025511004804?via%3Dihub

// Enum containing the different outcomes of calling fcbo_next_concept
enum OutputType {
    // Contains a newly computed formal concept and its calling context
    CallingContext(
        (BTreeSet<usize>, BTreeSet<usize>), // 1: touple containing one formal concept
        usize,                              // 2: the index of the inner for loop
        usize,                              // 3: current_node
    ),
    // Contains a new dead end attribute set and its current node
    DeadEndAttributes(
        BTreeSet<usize>, // 1: a new set of dead_end_attributes
        usize,           // 2: the index of the new set to determine position
    ),
    // Signals that a full node was cleared
    NodeCleared,
}

// New canonicity test added in paper to prevent duplicate branches
fn canonicity_test_one(
    smaller_subsets: &Vec<BTreeSet<usize>>,
    inner_index: usize,
    input_attributes: &BTreeSet<usize>,
    dead_end_attributes_set: &HashMap<(usize, usize), BTreeSet<usize>>,
    parent_node: usize,
) -> bool {
    dead_end_attributes_set.get(&(parent_node, inner_index))
    .unwrap()
    .intersection(&smaller_subsets[inner_index])
    .collect::<BTreeSet<&usize>>()
    .is_subset(&input_attributes.intersection(&smaller_subsets[inner_index])
    .collect())    
}

// Old canonicity test from paper
fn canonicity_test_two(
    smaller_subsets: &Vec<BTreeSet<usize>>,
    inner_index: usize,
    input_attributes: &BTreeSet<usize>,
    next_attributes: &BTreeSet<usize>,
) -> bool {
    input_attributes
    .intersection(&smaller_subsets[inner_index])
    .collect::<BTreeSet<&usize>>()
    ==
    next_attributes
    .intersection(&smaller_subsets[inner_index])
    .collect()
}


// Calculates a single OutputType enum
// Closely follows the pseudo code from paper but leaves out the halting condition which is checked in fcbo_concepts
fn fcbo_next_concept<T>(
    context: &FormalContext<T>,
    smaller_subsets: &Vec<BTreeSet<usize>>,
    input_attributes: &BTreeSet<usize>,
    inner_index: usize,
    dead_end_attributes_set: &HashMap<(usize, usize), BTreeSet<usize>>,
    parent_node: usize,
    current_node: usize,
) -> OutputType{

    for j in inner_index..context.attributes.len() {

        if !input_attributes.contains(&j) && canonicity_test_one(smaller_subsets,j, input_attributes, dead_end_attributes_set, parent_node) {

            let next_objects= context
            .index_attribute_derivation(input_attributes)
            .intersection(&context.index_attribute_derivation(&BTreeSet::from([j])))
            .cloned()
            .collect();
            let next_attributes = context.index_object_derivation(&next_objects);

            if canonicity_test_two(smaller_subsets, j, input_attributes, &next_attributes) {
                return OutputType::CallingContext((next_objects, next_attributes), j, current_node);
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
) -> impl Iterator<Item = (BTreeSet<usize>, BTreeSet<usize>)> + 'a {

    // Initializing the starting state needed for calling fcbo_next_concept 

    // Subsets needed by the canonicity tests from the paper
    let mut smaller_subsets: Vec<BTreeSet<usize>> = Vec::new();
    for i in 0..context.attributes.len() {
        smaller_subsets.push((0..i).collect());
    }
    // The first formal concept, usually ({"all objects"},{})
    let starting_objects = context.index_attribute_derivation(&BTreeSet::new());
    let mut input_attributes = context.index_object_derivation(&starting_objects);
    // Initial values for the first call of fcbo_next_concept
    let mut inner_index = 0;
    let mut parent_node = 0;
    let mut current_node: usize = 0;
    let mut total_nodes: usize = 0;
    // The first dead end attribue sets initialized to the empty set to always pass the first canonicity test
    let mut dead_end_attributes_set = HashMap::new();
    for i in 0..context.attributes.len() {
        dead_end_attributes_set.insert((current_node, i), BTreeSet::new());
    }
    // Queue containing all necessary information to call fcbo_next_concept
    let mut queue: VecDeque<(BTreeSet<usize>, usize, usize, usize)> = VecDeque::new();

    let mut first_concept = true;

    std::iter::from_fn(move || {
        // Returns the first concept and is then skipped
        if first_concept {
            first_concept = false;
            return Some((starting_objects.clone(), input_attributes.clone()));
        }
        // Loops until a new formal concept is returned by fcbo_next_concept
        loop {
            let output = fcbo_next_concept(context, &smaller_subsets, &input_attributes, inner_index, &dead_end_attributes_set, parent_node, current_node);

            match output {
                // 1: A new concept is added to the queue and the concept is returned
                OutputType::CallingContext(formal_concept, previous_inner_index, current_node) => {
                    // Checks the halting condition before adding the new concept to queue to prevent unnecessary queue entries
                    if formal_concept.1 != (0..context.attributes.len()).collect() && previous_inner_index < context.attributes.len() - 1 {
                        total_nodes += 1;
                        queue.push_back((formal_concept.1.clone(), previous_inner_index + 1 , total_nodes, current_node));
                    }
                    // Increments the index for the next call of fcbo_next_concept
                    inner_index = previous_inner_index + 1;
                    return Some(formal_concept);
                }
                // 2: Adds the new dead end attribute and increments the index for the next call of fcbo_next_concept
                OutputType::DeadEndAttributes(dead_end_attributes, previous_inner_index) => {
                    dead_end_attributes_set.insert((current_node, previous_inner_index), dead_end_attributes);
                    inner_index = previous_inner_index + 1;
                }
                // 3: Finishes the algorithm upon empty queue or updates the calling context of fcbo_next_concept
                OutputType::NodeCleared => {
                    if queue.len() < 1 {
                        return None;
                    }
                    // Processes the front queue entry
                    (input_attributes, inner_index, current_node, parent_node) = queue.pop_front().unwrap();
                    // Copies dead end attribute sets from the parent node if no set was added at the specific index in (2)
                    for i in inner_index..context.attributes.len() {
                        if !dead_end_attributes_set.contains_key(&(current_node, i)) {
                            dead_end_attributes_set.insert((current_node, i), dead_end_attributes_set.get(&(parent_node, i)).unwrap().clone());
                        }
                    }
                }
            }
        }
    })
}


#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fs};
    use itertools::Itertools;

    use crate::{algorithms::fcbo::fcbo_concepts, FormalContext};

    #[test]
    fn test_data_1() {
        let context = FormalContext::<String>::from(&fs::read("test_data/living_beings_and_water.cxt").unwrap()).unwrap();

        let concepts: BTreeSet<_> = fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BTreeSet<usize> = ms.into_iter().collect();
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
            let sub: BTreeSet<usize> = ms.into_iter().collect();
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
            let sub: BTreeSet<usize> = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }
}
