fn main() -> Result<(), Box<dyn std::error::Error>> {
    prost_build::compile_protos(&["proto/pg_logicaldec.proto"], &["proto/"])?;
    println!("cargo:rerun-if-changed=proto/pg_logicaldec.proto");
    Ok(())
}
