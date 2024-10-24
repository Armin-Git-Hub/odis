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
    IsFinished,
}

fn smaller_subset(inner_index: usize) -> BTreeSet<usize> {
    let mut subset = BTreeSet::new();
    for i in 0..inner_index {
        subset.insert(i);
    }
    subset
}

fn canonicity_test_one(
    inner_index: usize,
    input_attributes: &BTreeSet<usize>,
    dead_end_attributes_set: &HashMap<(usize, usize), BTreeSet<usize>>,
    parent_node: usize,
) -> bool {
    let y_j = smaller_subset(inner_index);
    dead_end_attributes_set.get(&(parent_node, inner_index))
    .unwrap()
    .intersection(&y_j)
    .cloned()
    .collect::<BTreeSet<usize>>()
    .is_subset(&input_attributes.intersection(&y_j)
    .cloned()
    .collect())    
}

fn canonicity_test_two(
    inner_index: usize,
    input_attributes: &BTreeSet<usize>,
    next_attributes: &BTreeSet<usize>,
) -> bool {
    input_attributes
    .intersection(&smaller_subset(inner_index))
    .collect::<BTreeSet<&usize>>()
    ==
    next_attributes
    .intersection(&smaller_subset(inner_index))
    .collect()
}

fn is_finished<T>(
    context: &FormalContext<T>,
    input_attributes: &BTreeSet<usize>,
    current_attribute: usize,
) -> bool {
    input_attributes == &(0..context.attributes.len()).collect()
    ||
    current_attribute > context.attributes.len()
}



fn fcbo_next_concept<T>(
    context: &FormalContext<T>,
    input_attributes: &BTreeSet<usize>,
    inner_index: usize,
    current_attribute: usize,
    dead_end_attributes_set: &HashMap<(usize, usize), BTreeSet<usize>>,
    parent_node: usize,
    current_node: usize,
) -> OutputType{

    if is_finished(context, input_attributes, current_attribute) {
        return  OutputType::IsFinished;
    }

    for j in inner_index..context.attributes.len() {
        if !input_attributes.contains(&j) && canonicity_test_one(j, input_attributes, dead_end_attributes_set, parent_node) {
            let next_objects= context
            .index_attribute_derivation(input_attributes)
            .intersection(&context.index_attribute_derivation(&BTreeSet::from([j])))
            .cloned()
            .collect();
            let next_attributes = context.index_object_derivation(&next_objects);

            if canonicity_test_two(j, input_attributes, &next_attributes) {
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

    let starting_objects = context.index_attribute_derivation(&BTreeSet::new());
    let mut input_attributes = context.index_object_derivation(&starting_objects);
    let mut global_inner_index = 0;
    let mut global_current_attribute = 0;
    let mut parent_node = 0;
    let mut current_node: usize = 0;
    let mut total_nodes: usize = 0;

    let mut dead_end_attributes_set = HashMap::new();
    for i in 0..context.attributes.len() {
        dead_end_attributes_set.insert((current_node, i), BTreeSet::new());
    }

    // 1: attribute set, 2: current attribute, 3: current node, 4: parent_node
    let mut queue: VecDeque<(BTreeSet<usize>, usize, usize, usize)> = VecDeque::new();

    let mut first_concept = true;

    std::iter::from_fn(move || {

        if first_concept {
            first_concept = false;
            return Some((starting_objects.clone(), input_attributes.clone()));
        }

        loop {
            
            let output = fcbo_next_concept(context, &input_attributes, global_inner_index, global_current_attribute, &dead_end_attributes_set, parent_node, current_node);

            match output {
                OutputType::CallingContext(formal_concept, inner_index, current_node) => {
                    total_nodes += 1;
                    // 1: attribute set, 2: current attribute, 3: current node, 4: parent_node
                    queue.push_back((formal_concept.1.clone(), inner_index + 1 , total_nodes, current_node));

                    global_inner_index = inner_index + 1;
                    return Some(formal_concept);
                }
                OutputType::DeadEndAttributes(dead_end_attributes, inner_index) => {
                    dead_end_attributes_set.insert((current_node, inner_index), dead_end_attributes);

                    global_inner_index = inner_index + 1;
                }
                OutputType::NodeCleared => {
                    let queue_entry: (BTreeSet<usize>, usize, usize, usize) = queue.pop_front().unwrap();
                    input_attributes = queue_entry.0;
                    global_current_attribute = queue_entry.1;
                    global_inner_index = global_current_attribute;
                    current_node = queue_entry.2;
                    parent_node = queue_entry.3;

                    for i in global_current_attribute..context.attributes.len() {
                        if !dead_end_attributes_set.contains_key(&(current_node, i)) {
                            dead_end_attributes_set.insert((current_node, i), dead_end_attributes_set.get(&(parent_node, i)).unwrap().clone());
                        }
                    }
                }
                OutputType::IsFinished => {
                    return None;
                }
            } // end of match
        }
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fs};
    use itertools::Itertools;

    use crate::{algorithms::fcbo::fcbo_concepts, FormalContext};

    #[test]
    fn test_concepts() {
        // living_beings_and_water
        // eu
        // data_from_paper
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();

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
