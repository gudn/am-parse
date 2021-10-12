use crate::parse::Expression;

trait Renderer {
  fn render(&mut self, expr: Expression);

  fn result(&self) -> String;
}

pub fn render(expr: Expression, output_format: crate::OutputFormat) -> String {
  unimplemented!()
}
