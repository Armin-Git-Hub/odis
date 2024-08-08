use std::collections::HashSet;

/// Graphs are important
pub struct Graph<T> {
    pub vertices: Vec<T>,
    pub edges: Vec<HashSet<usize>>,
}

impl<T> Graph<T> {
    /// Creates an empty graph.
    pub fn new() -> Self {
        Graph {
            vertices: Vec::new(),
            edges: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {}
