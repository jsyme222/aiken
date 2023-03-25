use aiken/builtin

pub fn length(self: ByteArray) -> Int {
  builtin.length_of_bytearray(self)
}

pub fn push(self: ByteArray, byte: Int) -> ByteArray {
  builtin.cons_bytearray(byte, self)
}
