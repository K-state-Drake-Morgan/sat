//! Everything to convert a string to a still slightly readable boolean problem

use std::{
    fs::File,
    io::{BufRead, BufReader},
};

use log::{debug, trace};

/// The possible human operands for a sat problem
pub enum HumanOperator {
    /// boolean and
    And,
    /// boolean or
    Or,
    /// boolean not
    Not,
    /// boolean implies
    Implies, // becomes not a or b
    /// boolean varible
    Variable(String),
    /// boolean true or false
    Constant(bool),
    /// (
    OpeningParenthesis,
    /// )
    ClosingParenthesis,
    /// [
    OpeningBracket,
    /// ]
    ClosingBracket,
    /// {
    OpeningCurly,
    /// }
    ClosingCurly,
}

impl HumanOperator {
    /// how much the operand matters
    pub fn precedence(&self) -> usize {
        match self {
            HumanOperator::Variable(_) => 0,
            HumanOperator::Not => 1,
            HumanOperator::And => 2,
            HumanOperator::Or => 3,
            HumanOperator::Implies => 4,
            _ => usize::MAX,
        }
    }

    /// effects precedence
    pub fn is_right_associative(&self) -> bool {
        matches!(self, HumanOperator::Implies | HumanOperator::Not)
    }
}

/// A human boolean problem
pub struct Sentance {
    /// The data
    pub data: Vec<HumanOperator>,
}

impl From<File> for Sentance {
    fn from(value: File) -> Self {
        trace!("Getting data from file");

        let mut data: Vec<HumanOperator> = Vec::new();
        let mut buffer = String::new();
        let mut reader = BufReader::with_capacity(4 * 1024 * 1024, value);
        let mut partial_utf8 = Vec::new(); // holds incomplete utf8 bytes between chunks

        loop {
            let consumed;
            {
                let buf = reader.fill_buf().expect("Unable to fill buffer");
                if buf.is_empty() {
                    break;
                }

                // Combine any leftover partial bytes with new chunk
                partial_utf8.extend_from_slice(buf);

                let (valid, incomplete) = match std::str::from_utf8(&partial_utf8) {
                    Ok(valid_str) => (valid_str, 0),
                    Err(e) => {
                        let valid_up_to = e.valid_up_to();
                        (
                            std::str::from_utf8(&partial_utf8[..valid_up_to]).unwrap(),
                            partial_utf8.len() - valid_up_to,
                        )
                    }
                };
                consumed = buf.len(); // store how many bytes to consume

                // Process only the valid UTF-8 part
                for ch in valid.chars() {
                    match ch {
                        '(' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::OpeningParenthesis);
                        }
                        ')' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::ClosingParenthesis);
                        }
                        '[' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::OpeningBracket);
                        }
                        ']' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::ClosingBracket);
                        }
                        '{' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::OpeningCurly);
                        }
                        '}' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::ClosingCurly);
                        }
                        '|' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::Or);
                        }
                        '&' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::And);
                        }
                        '!' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::Not);
                        }
                        '>' => {
                            push_buffer(&mut buffer, &mut data);
                            data.push(HumanOperator::Implies);
                        }
                        ' ' => {
                            push_buffer(&mut buffer, &mut data);
                        }
                        _ => buffer.push(ch),
                    }
                }
                partial_utf8.drain(..partial_utf8.len() - incomplete);
            }
            reader.consume(consumed);
            debug!("data has a length of: {}", data.len());
        }

        push_buffer(&mut buffer, &mut data);
        Sentance { data }
    }
}

impl From<String> for Sentance {
    fn from(value: String) -> Self {
        let mut data = Vec::with_capacity(value.len());
        let mut buffer = String::new();

        for ch in value.chars() {
            match ch {
                '(' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningParenthesis);
                }
                ')' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingParenthesis);
                }
                '[' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningBracket);
                }
                ']' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingBracket);
                }
                '{' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::OpeningCurly);
                }
                '}' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::ClosingCurly);
                }

                '|' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Or);
                }
                '&' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::And);
                }
                '!' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Not);
                }
                '>' => {
                    push_buffer(&mut buffer, &mut data);
                    data.push(HumanOperator::Implies);
                }

                ' ' => {
                    push_buffer(&mut buffer, &mut data);
                }

                _ => buffer.push(ch),
            }
        }

        push_buffer(&mut buffer, &mut data);

        Sentance { data }
    }
}

fn push_buffer(buffer: &mut String, data: &mut Vec<HumanOperator>) {
    if buffer.is_empty() {
        return;
    }

    let token = buffer.trim().to_lowercase();
    let op = match token.as_str() {
        "and" => HumanOperator::And,
        "or" => HumanOperator::Or,
        "not" => HumanOperator::Not,
        "implies" => HumanOperator::Implies,
        _ => HumanOperator::Variable(token),
    };
    data.push(op);
    buffer.clear();
}
