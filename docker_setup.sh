# Install curl (for installing rust) and build-essential (for building rust)
apt-get update
apt-get install -y \
  curl \
  build-essential

# Install rust
curl https://sh.rustup.rs -sSf | sh -s -- -y
source ~/.cargo/env

# Build the binary
cargo build --release --locked --bin combined_solver

echo "binary built in ./target/release/combined_solver"
