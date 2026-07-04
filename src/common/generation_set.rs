pub struct GenerationSet {
    data: Vec<u8>,
    generation: u8,
}

impl GenerationSet {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0; size],
            generation: 0,
        }
    }

    pub fn advance(&mut self) {
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            // clear to avoid false positives
            self.data.fill(0);
            self.generation = 1;
        }
    }

    pub fn insert(&mut self, idx: usize) {
        self.data[idx] = self.generation;
    }

    pub fn contains(&self, idx: usize) -> bool {
        self.data[idx] == self.generation
    }
}
