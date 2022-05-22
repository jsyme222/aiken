use crate::{encoder::Encoder, filler::Filler};

pub trait Encode {
    fn encode(&self, e: &mut Encoder) -> Result<(), String>;
}

impl Encode for bool {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.bool(*self);

        Ok(())
    }
}

impl Encode for u8 {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.u8(*self)?;

        Ok(())
    }
}

impl Encode for char {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.char(*self)?;

        Ok(())
    }
}

impl Encode for &str {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.string(*self)?;

        Ok(())
    }
}

impl Encode for String {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.string(self)?;

        Ok(())
    }
}

impl Encode for Vec<u8> {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.bytes(self)?;

        Ok(())
    }
}

impl Encode for &[u8] {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.bytes(self)?;

        Ok(())
    }
}

impl<T, K> Encode for (T, K)
where
    T: Encode,
    K: Encode,
{
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        self.0.encode(e)?;
        self.1.encode(e)?;

        Ok(())
    }
}

impl Encode for Filler {
    fn encode(&self, e: &mut Encoder) -> Result<(), String> {
        e.filler();

        Ok(())
    }
}
