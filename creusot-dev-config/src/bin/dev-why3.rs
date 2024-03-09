pub fn main() -> anyhow::Result<()> {
    let mut cmd = creusot_dev_config::why3_command()?;
    eprintln!("Using Why3 invocation: {:?}", cmd);
    let args = std::env::args().skip(1);
    cmd.args(args);
    cmd.status()?;
    Ok(())
}
