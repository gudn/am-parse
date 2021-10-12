use wasm_bindgen::prelude::*;

mod parse;
mod render;
mod tokens;
mod trie;

#[wasm_bindgen]
pub enum OutputFormat {
  Latex,
}

#[wasm_bindgen]
pub fn convert(
  input: String,
  output_format: OutputFormat,
  custom_functions: String,
) -> String {
  let tokens = tokens::tokenize(&input, custom_functions.split(" ").collect());
  let expr = parse::parse(tokens);
  render::render(expr, output_format)
}
