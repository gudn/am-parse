pub struct InputWrapper {
  data: Vec<char>,
  pos: usize,
}

impl InputWrapper {
  pub fn new(input: String) -> InputWrapper {
    InputWrapper {
      data: input.chars().collect(),
      pos: 0,
    }
  }

  pub fn mark(&self) -> usize {
    self.pos
  }

  pub fn reset(&mut self, mark: usize) {
    self.pos = mark
  }

  pub fn take(&mut self) -> Option<char> {
    if self.pos < self.data.len() {
      self.pos += 1;
      Some(self.data[self.pos - 1])
    } else {
      None
    }
  }

  pub fn peek(&self) -> Option<char> {
    if self.pos < self.data.len() {
      Some(self.data[self.pos])
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn test_wrapper() -> InputWrapper {
    InputWrapper::new("hello".into())
  }

  #[test]
  fn peek_not_change_pos() {
    let wrapper = test_wrapper();
    assert_eq!(wrapper.peek(), Some('h'));
    assert_eq!(wrapper.pos, test_wrapper().pos);
    assert_eq!(wrapper.mark(), test_wrapper().mark());
  }

  #[test]
  fn seq_take_return_all_string() {
    let mut wrapper = test_wrapper();
    assert_eq!(wrapper.take(), Some('h'));
    assert_eq!(wrapper.take(), Some('e'));
    assert_eq!(wrapper.take(), Some('l'));
    assert_eq!(wrapper.peek(), Some('l'));
    assert_eq!(wrapper.take(), Some('l'));
    assert_eq!(wrapper.take(), Some('o'));
    assert_eq!(wrapper.take(), None);
    assert_eq!(wrapper.take(), None);
    assert_eq!(wrapper.take(), None);
  }

  #[test]
  fn reset_move_pos() {
    let mut wrapper = test_wrapper();
    let m = wrapper.mark();
    assert_eq!(wrapper.take(), Some('h'));
    assert_eq!(wrapper.take(), Some('e'));
    wrapper.reset(m);
    assert_eq!(wrapper.take(), Some('h'));
    assert_eq!(wrapper.take(), Some('e'));
    let m = wrapper.mark();
    assert_eq!(wrapper.take(), Some('l'));
    assert_eq!(wrapper.take(), Some('l'));
    wrapper.reset(m);
    assert_eq!(wrapper.take(), Some('l'));
    assert_eq!(wrapper.take(), Some('l'));
    assert_eq!(wrapper.take(), Some('o'));
    assert_eq!(wrapper.take(), None);
    let m = wrapper.mark();
    assert_eq!(wrapper.take(), None);
    wrapper.reset(m);
    assert_eq!(wrapper.take(), None);
  }
}
