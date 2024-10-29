use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::FormalContext;

enum OutputType {
    CallingContext(
        (BTreeSet<usize>, BTreeSet<usize>), // 1: touple containing one formal concept
        usize,                              // 2: the index of the inner for loop
        usize,                              // 3: current_node
    ),
    DeadEndAttributes(
        BTreeSet<usize>, // 1: a new set of dead_end_attributes
        usize,           // 2: the index of the new set to determine position
    ),
    NodeCleared,
}

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


pub fn fcbo_concepts<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = (BTreeSet<usize>, BTreeSet<usize>)> + 'a {


    let mut smaller_subsets: Vec<BTreeSet<usize>> = Vec::new();
    for i in 0..context.attributes.len() {
        smaller_subsets.push((0..i).collect());
    }
    let starting_objects = context.index_attribute_derivation(&BTreeSet::new());
    let mut input_attributes = context.index_object_derivation(&starting_objects);
    let mut inner_index = 0;
    let mut parent_node = 0;
    let mut current_node: usize = 0;
    let mut total_nodes: usize = 0;
    let mut dead_end_attributes_set = HashMap::new();
    for i in 0..context.attributes.len() {
        dead_end_attributes_set.insert((current_node, i), BTreeSet::new());
    }
    let mut queue: VecDeque<(BTreeSet<usize>, usize, usize, usize)> = VecDeque::new();

    let mut first_concept = true;

    std::iter::from_fn(move || {
        if first_concept {
            first_concept = false;
            return Some((starting_objects.clone(), input_attributes.clone()));
        }
        loop {
            
            let output = fcbo_next_concept(context, &smaller_subsets, &input_attributes, inner_index, &dead_end_attributes_set, parent_node, current_node);

            match output {
                OutputType::CallingContext(formal_concept, previous_inner_index, current_node) => {
                    if formal_concept.1 != (0..context.attributes.len()).collect() && previous_inner_index < context.attributes.len() - 1 {
                        total_nodes += 1;
                        queue.push_back((formal_concept.1.clone(), previous_inner_index + 1 , total_nodes, current_node));
                    }
                    inner_index = previous_inner_index + 1;
                    return Some(formal_concept);
                }
                OutputType::DeadEndAttributes(dead_end_attributes, previous_inner_index) => {
                    dead_end_attributes_set.insert((current_node, previous_inner_index), dead_end_attributes);
                    inner_index = previous_inner_index + 1;
                }
                OutputType::NodeCleared => {
                    if queue.len() < 1 {
                        return None;
                    }
                    (input_attributes, inner_index, current_node, parent_node) = queue.pop_front().unwrap();
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
