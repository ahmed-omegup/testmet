fn main() {
    // We'll manually define the proto structs in Rust instead of using .proto files
    // This is simpler than parsing the decoderbufs proto files
    println!("cargo:rerun-if-changed=build.rs");
}
