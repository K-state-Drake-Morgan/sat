//! to allow for benching
use log::debug;
use std::path::PathBuf;

pub mod solver;

/// for more information on cnf files see:
/// https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html
pub fn from_cnf(file_path: &PathBuf) -> String {
    debug!("CNF File");

    let temp = std::fs::read_to_string(file_path).expect("Unable to read file");
    let mut result = String::new();
    let mut current_clause: Vec<String> = Vec::new();

    for line in temp.lines() {
        let line = line.trim();

        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue;
        }

        for token in line.split_whitespace() {
            if token == "0" {
                if !current_clause.is_empty() {
                    result.push('(');
                    result.push_str(&current_clause.join("|"));
                    result.push(')');
                    result.push('&');
                    current_clause.clear();
                }
            } else if token.starts_with('-') {
                let new = &token[1..token.len()];
                current_clause.push(format!("!{}", new));
            } else {
                current_clause.push(format!("{}", token));
            }
        }
    }

    while result.ends_with('&') {
        result.pop();
    }

    result
}
