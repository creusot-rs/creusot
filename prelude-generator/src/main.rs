use std::{
    env, fs,
    fs::{File, copy, create_dir_all, read_to_string},
    io::{self, BufWriter, Write},
    path::{Path, PathBuf},
};

// This needs to run when installing Creusot of course,
// and also before replaying the proofs in the test suite.
fn main() -> anyhow::Result<()> {
    println!("Building prelude...");

    // Get the path  to the crate directory
    let crate_dirpath = PathBuf::from(env::var("CARGO_MANIFEST_DIR")?);
    let tgt_prelude_dirpath = crate_dirpath.join("..").join("target").join("creusot");
    create_dir_all(&tgt_prelude_dirpath)?;

    let src_prelude_dirpath = crate_dirpath.join("..").join("prelude-generator");

    // Create integer prelude
    let int_template_filepath = src_prelude_dirpath.join("int.in.coma");
    int_prelude_maker(&int_template_filepath, &tgt_prelude_dirpath.join("int.coma"))?;

    // Create slice prelude
    let slice_template_filepath = src_prelude_dirpath.join("slice.in.coma");
    slice_prelude_maker(&slice_template_filepath, &tgt_prelude_dirpath.join("slice.coma"))?;

    // Copy prelude in target directory
    copy_if_newer(
        src_prelude_dirpath.join("prelude.coma"),
        tgt_prelude_dirpath.join("prelude.coma"),
    )?;
    copy_if_newer(src_prelude_dirpath.join("float.coma"), tgt_prelude_dirpath.join("float.coma"))?;

    // Copy why3find conf in target directory
    copy_if_newer(
        crate_dirpath.join("..").join("why3find.json"),
        crate_dirpath.join("..").join("target").join("why3find.json"),
    )?;

    Ok(())
}

fn copy_if_newer(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    let src_meta = fs::metadata(&src)?;
    if let Ok(dst_meta) = fs::metadata(&dst) {
        if src_meta.modified().unwrap() <= dst_meta.modified().unwrap() {
            return Ok(());
        }
    }
    copy(src, dst).unwrap();
    Ok(())
}

fn int_prelude_maker(template_filepath: &Path, int_prelude_filepath: &Path) -> io::Result<()> {
    let template = read_to_string(template_filepath)?;

    let file = File::create(int_prelude_filepath)?;
    let mut writer = BufWriter::new(file);

    // take the template and replace each variable for integer type (signed and unsigned)
    let mut write_modules = |bits_count| {
        let min_signed_value = format!("0x{:X}", 1u128 << (bits_count - 1));
        let max_signed_value = format!("0x{:X}", (1u128 << (bits_count - 1)) - 1);
        let max_unsigned_value = format!("0x{:X}", 1u128.unbounded_shl(bits_count).wrapping_sub(1));

        let r = template.replace("$bits_count$", &bits_count.to_string());
        let r = r.replace("$min_signed_value$", &min_signed_value);
        let r = r.replace("$max_signed_value$", &max_signed_value);
        let r = r.replace("$max_unsigned_value$", &max_unsigned_value);
        let s = String::from("0x1")
            + &std::iter::repeat_n("0", bits_count as usize / 4).collect::<String>();
        let r = r.replace("$two_power_size$", &s);

        writer.write_all(r.as_bytes())?;
        writeln!(writer)
    };

    write_modules(8)?;
    write_modules(16)?;
    write_modules(32)?;
    write_modules(64)?;
    write_modules(128)
}

fn slice_prelude_maker(template_filepath: &Path, slice_prelude_filepath: &Path) -> io::Result<()> {
    let template = read_to_string(template_filepath)?;

    let file = File::create(slice_prelude_filepath)?;
    let mut writer = BufWriter::new(file);

    // take the template and replace each variable for integer type (signed and unsigned)
    let mut write_modules = |bits_count: u8| {
        let bits_count = bits_count.to_string();

        let r = template.replace("$bits_count$", &bits_count);

        writer.write_all(r.as_bytes())?;
        writeln!(writer)
    };

    write_modules(16)?;
    write_modules(32)?;
    write_modules(64)
}
