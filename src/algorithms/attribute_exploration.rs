use bit_set::BitSet;
use std::io::{self, Write};

use crate::FormalContext;

use super::canonical_basis;

fn first_question(context: &FormalContext<String>, question: (&BitSet, &BitSet)) -> bool {
    let mut premise: Vec<String> = Vec::new();
    for index in question.0 {
        premise.push(context.attributes[index].to_string());
    }
    let mut conclusion: Vec<String> = Vec::new();
    for index in question.1 {
        conclusion.push(context.attributes[index].to_string());
    }

    print!("{esc}[2J{esc}[1;1H", esc = 27 as char);
    loop {
        let mut answer = String::new();

        println!("Is the following implication valid?");
        println!("  {:?} -> {:?}", premise, conclusion);

        io::stdout()
            .write(b"Please enter your answer (\"yes\", \"no\"): ")
            .unwrap();
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut answer).unwrap();

        print!("{esc}[2J{esc}[1;1H", esc = 27 as char);

        match answer.trim() {
            "yes" => return true,
            "no" => return false,
            _ => {
                println!("Please only answer with: \"yes\" or \"no\"!\n");
            }
        }
    }
}

fn second_question(context: &FormalContext<String>) -> (String, BitSet) {
    print!("{esc}[2J{esc}[1;1H", esc = 27 as char);

    let mut object = String::new();
    let mut attributes = String::new();
    let mut attributes_set = BitSet::new();

    loop {
        object.clear();
        io::stdout().write(b"Enter name of new object: ").unwrap();
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut object).unwrap();

        print!("{esc}[2J{esc}[1;1H", esc = 27 as char);

        if object.is_ascii() {
            break;
        } else {
            println!("Please only use ASCII characters.")
        }
    }

    'a: loop {
        attributes.clear();
        io::stdout().write(
            b"Name all attributes this object posesses.\nPlease use the following format: \"1. attr, 2. attr, 3. attr, ...\"\n"
        ).unwrap();
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut attributes).unwrap();

        print!("{esc}[2J{esc}[1;1H", esc = 27 as char);

        let names: Vec<&str> = attributes
            .trim()
            .split(",")
            .filter_map(|x| {
                if x == "" {
                    return None;
                }
                Some(x.trim())
            })
            .collect();

        for name in names {
            let valid_name = match context.attributes.iter().position(|r| r.as_str() == name) {
                Some(index) => attributes_set.insert(index),
                None => false,
            };
            if !valid_name {
                println!("Please only enter valid attribute names.\n");
                break;
            } else {
                break 'a;
            }
        }
    }
    object = object.trim().to_string();

    (object, attributes_set)
}

pub fn attribute_exploration(context: &mut FormalContext<String>) -> Vec<(BitSet, BitSet)> {
    let mut basis: Vec<(BitSet, BitSet)> = Vec::new();
    let mut temp_set = BitSet::new();

    while temp_set != (0..context.attributes.len()).collect() {
        let temp_set_hull = context.index_attribute_hull(&temp_set);
        while temp_set != temp_set_hull {
            if first_question(
                &context,
                (&temp_set, &temp_set_hull.difference(&temp_set).collect()),
            ) {
                basis.push((temp_set.clone(), temp_set_hull));
                break;
            } else {
                let (new_object, attributes) = second_question(&context);
                context.add_object(new_object, &attributes);
            }
        }
        temp_set = canonical_basis::next_preclosure(context, &basis, &temp_set)
    }
    basis
}
