use aiken/bytearray.{length}

validator {
  fn foo(_rdmr: Data, _ctx: Data) {
    length(#[
        1, 2, 3]) == 3 && bytearray.push(#[
        ], 1) == #[
      1] && bytearray.push(byte: 14, self: #[0, 0, 0]) == #[0, 0, 0, 14]
  }
}
