pub trait Render {
  fn render(&self, output_format: crate::OutputFormat) -> String;
}
