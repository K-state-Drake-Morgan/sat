use color_eyre::Result;
use crossterm::{
    event::{self, Event, KeyCode, KeyEvent, KeyModifiers},
    terminal::{disable_raw_mode, enable_raw_mode},
};
use num_traits::Zero;
use ratatui::{
    DefaultTerminal, Frame,
    prelude::*,
    widgets::{Block, Borders, Paragraph, Wrap},
};
use sat::solver::formula::Formula;

pub fn run(mut terminal: DefaultTerminal, starting_equation: String) -> Result<()> {
    enable_raw_mode()?;

    let mut app = App::default();

    app.input = starting_equation;

    loop {
        terminal.draw(|frame| render(frame, &app))?;

        match event::read()? {
            Event::Key(KeyEvent {
                code, modifiers, ..
            }) => match (code, modifiers) {
                // --- Exit ---
                (KeyCode::Char('q'), KeyModifiers::CONTROL) | (KeyCode::Esc, _) => break,

                // --- Actions ---
                (KeyCode::Char('s'), KeyModifiers::CONTROL)
                | (KeyCode::Enter, KeyModifiers::CONTROL) => app.solve(),
                (KeyCode::Char('d'), KeyModifiers::CONTROL) => app.deduce(),

                // --- Text editing ---
                (KeyCode::Backspace, _) => {
                    app.input.pop();
                }
                (KeyCode::Char(c), _) if modifiers.is_empty() => app.input.push(c),

                // --- Scroll INPUT (no modifiers) ---
                (KeyCode::Up, KeyModifiers::NONE) => {
                    app.input_scroll_y = app.input_scroll_y.saturating_sub(1)
                }
                (KeyCode::Down, KeyModifiers::NONE) => {
                    app.input_scroll_y = app.input_scroll_y.saturating_add(1)
                }
                (KeyCode::Left, KeyModifiers::NONE) => {
                    app.input_scroll_x = app.input_scroll_x.saturating_sub(1)
                }
                (KeyCode::Right, KeyModifiers::NONE) => {
                    app.input_scroll_x = app.input_scroll_x.saturating_add(1)
                }
                (KeyCode::PageUp, KeyModifiers::NONE) => {
                    app.input_scroll_y = app.input_scroll_y.saturating_sub(5)
                }
                (KeyCode::PageDown, KeyModifiers::NONE) => {
                    app.input_scroll_y = app.input_scroll_y.saturating_add(5)
                }

                // --- Scroll RESULT (with Ctrl) ---
                (KeyCode::Up, KeyModifiers::CONTROL) => {
                    app.result_scroll_y = app.result_scroll_y.saturating_sub(1)
                }
                (KeyCode::Down, KeyModifiers::CONTROL) => {
                    app.result_scroll_y = app.result_scroll_y.saturating_add(1)
                }
                (KeyCode::Left, KeyModifiers::CONTROL) => {
                    app.result_scroll_x = app.result_scroll_x.saturating_sub(1)
                }
                (KeyCode::Right, KeyModifiers::CONTROL) => {
                    app.result_scroll_x = app.result_scroll_x.saturating_add(1)
                }
                (KeyCode::PageUp, KeyModifiers::CONTROL) => {
                    app.result_scroll_y = app.result_scroll_y.saturating_sub(5)
                }
                (KeyCode::PageDown, KeyModifiers::CONTROL) => {
                    app.result_scroll_y = app.result_scroll_y.saturating_add(5)
                }

                _ => {}
            },
            _ => {}
        }
    }

    disable_raw_mode()?;
    Ok(())
}

#[derive(Default)]
struct App {
    input: String,
    result_lines: Vec<Line<'static>>,
    error: Option<String>,

    // Scroll state for input
    input_scroll_y: u16,
    input_scroll_x: u16,

    // Scroll state for results
    result_scroll_y: u16,
    result_scroll_x: u16,
}

impl App {
    fn solve(&mut self) {
        match Formula::try_from(self.input.clone()) {
            Ok(f) => match f.fully_solve() {
                Some(model) if !model.is_zero() => {
                    let mut lines = vec![
                        Line::from(Span::styled(
                            "Satisfiable",
                            Style::default().fg(Color::Green),
                        )),
                        Line::from("──────────────"),
                    ];
                    let bits = format!("{:0b}", model);
                    let mut bit_chars: Vec<char> = bits.chars().rev().collect();
                    while bit_chars.len() < f.names.len() {
                        bit_chars.push('0');
                    }
                    let max_names_length = f
                        .names
                        .iter()
                        .max_by(|left, right| left.len().cmp(&right.len()))
                        .unwrap_or(&"".to_string())
                        .len();
                    for (i, name) in f.names.iter().enumerate() {
                        let bit = bit_chars[i];
                        let val = if bit == '1' { "true" } else { "false" };

                        lines.push(Line::from(format!(
                            "{: <2$} = {}",
                            name, val, max_names_length
                        )));
                    }
                    self.result_lines = lines;
                    self.error = None;
                }
                _ => {
                    self.result_lines = vec![Line::from(Span::styled(
                        "Unsatisfiable",
                        Style::default().fg(Color::Red),
                    ))];
                    self.error = None;
                }
            },
            Err(e) => {
                self.error = Some(format!("{}", e));
                self.result_lines.clear();
            }
        }
    }

    fn deduce(&mut self) {
        match Formula::try_from(self.input.clone()) {
            Ok(f) => match f.deduce() {
                Some(model) if !model.is_zero() => {
                    let mut lines = vec![
                        Line::from(Span::styled(
                            "Deduction found",
                            Style::default().fg(Color::Green),
                        )),
                        Line::from("──────────────"),
                    ];
                    let bits = format!("{:0b}", model);
                    let mut bit_chars: Vec<char> = bits.chars().rev().collect();
                    while bit_chars.len() < f.names.len() {
                        bit_chars.push('0');
                    }
                    let max_names_length = f
                        .names
                        .iter()
                        .max_by(|left, right| left.len().cmp(&right.len()))
                        .unwrap_or(&"".to_string())
                        .len();
                    for (i, name) in f.names.iter().enumerate() {
                        let bit = bit_chars[i];
                        let val = if bit == '1' { "true" } else { "false" };

                        lines.push(Line::from(format!(
                            "{: <2$} = {}",
                            name, val, max_names_length
                        )));
                    }
                    self.result_lines = lines;
                    self.error = None;
                }
                _ => {
                    self.result_lines = vec![Line::from(Span::styled(
                        "❌ Could not deduce a solution",
                        Style::default().fg(Color::Red),
                    ))];
                    self.error = None;
                }
            },
            Err(e) => {
                self.error = Some(format!("{}", e));
                self.result_lines.clear();
            }
        }
    }
}

fn render(frame: &mut Frame, app: &App) {
    let area = frame.area();

    let layout = Layout::vertical([
        Constraint::Length(5),
        Constraint::Min(5),
        Constraint::Length(2),
    ])
    .split(area);

    // --- Formula input box ---
    let input_box = Paragraph::new(app.input.as_str())
        .block(Block::default().borders(Borders::ALL).title("Formula"))
        .wrap(Wrap { trim: false }) // allow horizontal scrolling
        .scroll((app.input_scroll_y, app.input_scroll_x)); // 🔽 add scrolling
    frame.render_widget(input_box, layout[0]);

    // --- Result box ---
    let mut result_widget = if let Some(err) = &app.error {
        let in_lines = err.lines();
        let mut out_lines: Vec<Line> = Vec::new();
        for line in in_lines {
            out_lines.push(Line::styled(line, Style::default().fg(Color::Red)));
        }
        Paragraph::new(out_lines)
            .block(Block::default().borders(Borders::ALL).title("Error"))
            .wrap(Wrap { trim: false })
    } else if !app.result_lines.is_empty() {
        Paragraph::new(app.result_lines.clone())
            .block(Block::default().borders(Borders::ALL).title("Result"))
            .wrap(Wrap { trim: false })
    } else {
        Paragraph::new("Press [s] to Solve or [d] to Deduce")
            .block(Block::default().borders(Borders::ALL).title("Result"))
    };

    // 🔽 Apply scroll offset for the result area
    result_widget = result_widget.scroll((app.result_scroll_y, app.result_scroll_x));

    frame.render_widget(result_widget, layout[1]);

    // --- Help line ---
    let help_text = "Keys: [↑↓←→] Scroll Input: [Ctrl+↑↓←→] Scroll Result | [Ctrl+s] Solve [Ctrl+d] Deduce [Ctrl+q] Quit";
    let help = Paragraph::new(help_text).style(Style::default().fg(Color::DarkGray));
    frame.render_widget(help, layout[2]);
}
