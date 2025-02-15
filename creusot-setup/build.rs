#![feature(try_blocks, unbounded_shifts)]

use std::{
    env,
    error::Error,
    fs::{copy, create_dir_all, read_to_string, File},
    io::{self, BufWriter, Write},
    path::{Path, PathBuf},
    result::Result,
};

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

        writer.write(r.as_bytes())?;
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

        writer.write(r.as_bytes())?;
        writeln!(writer)
    };

    write_modules(16)?;
    write_modules(32)?;
    write_modules(64)
}

fn main() {
    let result: Result<(), Box<dyn Error>> = try {
        // rerun this build script if it has changed
        println!("cargo:rerun-if-changed=build.rs");

        // Get the path  to the crate directory
        let crate_dirpath = PathBuf::from(env::var("CARGO_MANIFEST_DIR")?);
        let tgt_prelude_dirpath = crate_dirpath.join("..").join("target").join("prelude");
        create_dir_all(&tgt_prelude_dirpath)?;

        let src_prelude_dirpath = crate_dirpath.join("..").join("prelude");

        // Create integer prelude
        let int_template_filepath = src_prelude_dirpath.join("int.in.coma");
        println!("cargo:rerun-if-changed=../prelude/int.in.coma");
        int_prelude_maker(&int_template_filepath, &tgt_prelude_dirpath.join("int.coma"))?;

        // Create slice prelude
        let slice_template_filepath = src_prelude_dirpath.join("slice.in.coma");
        println!("cargo:rerun-if-changed=../prelude/slice.in.coma");
        slice_prelude_maker(&slice_template_filepath, &tgt_prelude_dirpath.join("slice.coma"))?;

        // Copy prelude in target directory
        copy(src_prelude_dirpath.join("prelude.coma"), tgt_prelude_dirpath.join("prelude.coma"))?;
        copy(src_prelude_dirpath.join("float.coma"), tgt_prelude_dirpath.join("float.coma"))?;

        // Copy why3find conf in target directory
        copy(
            crate_dirpath.join("..").join("why3find.json"),
            crate_dirpath.join("..").join("target").join("why3find.json"),
        )?;
    };

    result.unwrap_or_else(|e| {
        eprintln!("Error when creating preludes: {}", e);
        std::process::exit(1)
    })
}
