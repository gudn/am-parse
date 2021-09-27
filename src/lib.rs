use wasm_bindgen::prelude::*;

mod trie;
mod tokens;

#[wasm_bindgen]
pub enum OutputFormat {
  Latex,
}

#[wasm_bindgen]
pub fn convert(input: String, _output_format: OutputFormat) -> String {
  let _tokens = tokens::tokenize(&input);
  unimplemented!()
}
