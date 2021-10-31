use am_parse::{convert, OutputFormat};

use std::env::args;
use std::io::stdin;

fn main() {
  let mut input = String::new();
  let mut custom_functions = Vec::new();
  for arg in args().skip(1) {
    if input.is_empty() && arg == "--" {
      input.push(' ');
    } else {
      let cf = if input.is_empty() {
        arg.strip_prefix("-C")
      } else {
        None
      };
      if let Some(cf) = cf {
        custom_functions.push(cf.to_string());
      } else {
        input.push_str(&arg);
      }
    }
  }
  if input.is_empty() {
    stdin()
      .read_line(&mut input)
      .expect("failed to read from stdin");
  }
  let trimmed = input.trim();
  if trimmed.is_empty() {
    panic!("empty input");
  }
  let output = convert(
    trimmed.to_string(),
    OutputFormat::Latex,
    custom_functions.iter().map(AsRef::as_ref).collect(),
  );
  println!("{}", output);
}
