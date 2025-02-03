use std::{env, error::Error, fs::{self, File}, io::{self, Write}, path::{Path, PathBuf}};
use indoc::indoc;

fn int_prelude_maker(filepath: &impl AsRef<Path>) -> Result<(), Box<dyn Error>> {
    // generate coma code for unsigned integer
    macro_rules! uint_mod {
        ($writer: ident, $n: literal) => {
            ::paste::paste! {
                let m = format!(indoc! {r#"
                module {module_name}
                    use export bv.{BV_name}
                    use bv.BV256 as BV256
                    use bv.{BVConverter_name}
                    use int.Int
                    use int.EuclideanDivision as ED
    
                    constant max_uint : t = 0x{max_value:X}
                    function to_BV256 (x: t) : BV256.t = toBig x
                    function of_BV256 (x: BV256.t) : t = toSmall x
                    function bv256_to_int (x: BV256.t) : int = BV256.t'int x
                    constant max_uint_as_BV256 : BV256.t = to_BV256 max_uint
    
                    let eq (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a = t'int b }} {{ result <-> a = b }}) = any
                    let ne (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a <> t'int b }} {{ result <-> a <> b }}) = any
                    let le (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a <= t'int b }}  {{ result <-> ule a b }}) = any
                    let lt (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a < t'int b }} {{ result <-> ult a b }}) = any
                    let ge (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a >= t'int b }} {{ result <-> uge a b }}) = any
                    let gt (a: t) (b: t) (ret (result: bool) {{ result <-> t'int a > t'int b }} {{ result <-> ugt a b }}) = any
                    
                    let add (a:t) (b:t)
                        {{ [@expl:arithmetic overflow] t'int a + t'int b < two_power_size \/ BV256.ule (BV256.add (to_BV256 a) (to_BV256 b)) max_uint_as_BV256 }}
                        (ret (result :t)  {{ t'int result = t'int a + t'int b }} {{ result = add a b }})
                        = any
                    let sub (a:t)  (b:t)
                        {{ [@expl:arithmetic overflow] t'int a >= t'int b \/ uge a b }}
                        (ret (result: t) {{ t'int result = t'int a - t'int b }} {{ result = sub a b }})
                        = any
                    let mul (a:t) (b:t)
                        {{ [@expl:arithmetic overflow] t'int a * t'int b < two_power_size \/ BV256.ule (BV256.mul (to_BV256 a) (to_BV256 b)) max_uint_as_BV256 }}
                        (ret (result: t) {{ result = mul a b }} {{ t'int result = t'int a * t'int b }})
                        = any
                    let div (a:t) (b:t)
                        {{ [@expl:division by zero] b <> zeros \/ t'int b <> 0 }}
                        (ret (result: t) {{ t'int result = ED.div (t'int a) (t'int b) }} {{ result = udiv a b }})
                        = any
                    let rem (a:t) (b:t)
                        {{ [@expl:remainder by zero] b <> zeros  \/ t'int b <> 0 }}
                        (ret (result: t) {{ t'int result = ED.mod (t'int a) (t'int b) }} {{ result = urem a b }})
                        = any
    
                    let bw_and (a:t) (b:t) (ret (result :t)) = ret {{ bw_and a b }}
                    let bw_or (a:t) (b:t) (ret (result :t)) = ret {{ bw_or a b }}
                    let bw_xor (a:t) (b:t) (ret (result :t)) = ret {{ bw_xor a b }}
                    let bw_not (a:t) (ret (result :t)) = ret {{ bw_not a }}
                    let shl (a:t) (b:int)
                        {{ [@expl:out-of-bounds shifting] b >= 0 /\ b <= size  }}
                        (ret (result :t) {{ result = lsl_bv a (of_int b) }} {{ result = lsl a b }})
                        = any
                    let shr (a:t) (b:int)
                        {{ [@expl:out-of-bounds shifting] b >= 0 /\ b <= size }}
                        (ret (result :t) {{ result = lsr_bv a (of_int b) }} {{ result = lsr a b }})
                        = any
    
                    let to_bv256 (a:t)
                        (ret (result: BV256.t) {{ result = to_BV256 a }})
                        = any
                    let of_bv256 (a:BV256.t)
                        {{ [@expl:arithmetic overflow] bv256_to_int a >= 0 /\ bv256_to_int a < two_power_size }}
                        (ret (result: t) {{ result = of_BV256 a }})
                        = any
                end
                "#}, module_name = stringify!([<UInt $n>]), BV_name = stringify!([<BV $n>]), BVConverter_name = stringify!([<BVConverter_ $n _256>]), max_value = [<u $n>]::MAX);
    
                $writer.write_all(m.as_bytes())?;
            }
        };
    }
    
    // generate coma code for signed integer
    macro_rules! int_mod {
        ($writer: ident, $n: literal) => {
            ::paste::paste! {
                let m = format!(indoc! {r#"
                module {module_name}
                    use export bv.{BV_name}
                    use bv.BV256 as BV256
                    use bv.{BVConverter_name}
                    use bv.Pow2int
                    use int.Int
                    use int.ComputerDivision as CD
    
                    constant min_sint : t = 0x{min_value:X}
                    constant max_sint : t = 0x{max_value:X}
                    constant minus_one : t = 0x{max_uint_value:X}
    
                    function to_BV256 (x: t) : BV256.t = stoBig x
                    function of_BV256 (x: BV256.t) : t = toSmall x
                    function bv256_to_int (x: BV256.t) : int = BV256.to_int x
                    constant min_sint_as_BV256 : BV256.t = to_BV256 min_sint
                    constant max_sint_as_BV256 : BV256.t = to_BV256 max_sint
    
                    let eq (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a = to_int b }} {{ result <-> a = b }}) = any
                    let ne (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a <> to_int b }} {{ result <-> a <> b }}) = any
                    let le (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a <= to_int b }}  {{ result <-> sle a b }}) = any
                    let lt (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a < to_int b }} {{ result <-> slt a b }}) = any
                    let ge (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a >= to_int b }} {{ result <-> sge a b }}) = any
                    let gt (a: t) (b: t) (ret (result: bool) {{ result <-> to_int a > to_int b }} {{ result <-> sgt a b }}) = any
    
                    let neg (a:t) 
                        {{ [@expl:arithmetic overflow] a <> min_sint }}
                        (ret (result :t)  {{ to_int result = - to_int a  }} {{ result = neg a}})
                        = any
                    let add (a:t) (b:t)
                        {{ [@expl:arithmetic overflow] - two_power_size_minus_one <= to_int a + to_int b < two_power_size_minus_one \/ let r = BV256.add (to_BV256 a) (to_BV256 b) in (BV256.sle min_sint_as_BV256 r /\ BV256.sle r max_sint_as_BV256) }}
                        (ret (result :t)  {{ to_int result = to_int a + to_int b }} {{ result = add a b }})
                        = any
                    let sub (a:t)  (b:t)
                        {{ [@expl:arithmetic overflow] - two_power_size_minus_one <= to_int a - to_int b < two_power_size_minus_one \/ let r = BV256.sub (to_BV256 a) (to_BV256 b) in (BV256.sle min_sint_as_BV256 r /\ BV256.sle r max_sint_as_BV256) }}
                        (ret (result: t) {{ to_int result = to_int a - to_int b }} {{ result = sub a b }})
                        = any
                    let mul (a:t) (b:t)
                        {{ [@expl:arithmetic overflow] - two_power_size_minus_one <= to_int a * to_int b < two_power_size_minus_one \/ let r = BV256.mul (to_BV256 a) (to_BV256 b) in (BV256.sle min_sint_as_BV256 r /\ BV256.sle r max_sint_as_BV256) }}
                        (ret (result: t) {{ to_int result = to_int a * to_int b }} {{ result = mul a b }})
                        = any
                    let div (a:t) (b:t)
                        {{ [@expl:division by zero] b <> zeros  \/ to_int b <> 0 }}
                        {{ [@expl:signed division overflow check] (a <> min_sint \/ b <> minus_one) \/ (to_int a <> to_int min_sint \/ to_int b <> -1) }}
                        (ret (result: t) {{ to_int result = CD.div (to_int a) (to_int b) }} {{ result = sdiv a b }})
                        = any
                    let rem (a:t) (b:t)
                        {{ [@expl:remainder by zero] b <> zeros \/ to_int b <> 0 }}
                        (ret (result: t) {{ to_int result = CD.mod (to_int a) (to_int b) }} {{ result = srem a b }})
                        = any
    
                    let bw_and (a:t) (b:t) (ret (result :t)) = ret {{ bw_and a b }}
                    let bw_or (a:t) (b:t) (ret (result :t)) = ret {{ bw_or a b }}
                    let bw_xor (a:t) (b:t) (ret (result :t)) = ret {{ bw_xor a b }}
                    let bw_not (a:t) (ret (result :t)) = ret {{ bw_not a }}
                    let shl (a:t) (b:int)
                        {{ [@expl:out-of-bounds shifting] ult (of_int b) size_bv \/ b < size  }}
                        {{ [@expl:out-of-bounds shifting] sle zeros a \/ to_int a >= 0 }}
                        {{ [@expl:arithmetic overflow] (to_int a) * (pow2 (b)) < two_power_size_minus_one \/ let r = BV256.lsl_bv (to_BV256 a) (to_BV256 (of_int b)) in (BV256.sle min_sint_as_BV256 r /\ BV256.sle r max_sint_as_BV256)}}
                        (ret (result :t) {{ result = lsl_bv a (of_int b) }} {{ result = lsl a b }})
                        = any
                    let shr (a:t) (b:int)
                        {{ [@expl:out-of-bounds shifting] ult (of_int b) size_bv \/ b < size }}
                        (ret (result :t) {{ result = asr_bv a (of_int b) }} {{ result = asr a b }})
                        = any
    
                    let to_bv256 (a:t)
                        (ret (result: BV256.t) {{ result = to_BV256 a }})
                        = any
                    let of_bv256 (a:BV256.t)
                        {{ [@expl:arithmetic overflow] bv256_to_int a >= 0 /\ bv256_to_int a < two_power_size }}
                        (ret (result: t) {{ result = of_BV256 a }})
                        = any
                end
                "#}, module_name = stringify!([<Int $n>]), BV_name = stringify!([<BV $n>]), BVConverter_name = stringify!([<BVConverter_ $n _256>]), min_value = [<i $n>]::MIN, max_value = [<i $n>]::MAX, max_uint_value= [<u $n>]::MAX);
    
                $writer.write_all(m.as_bytes())?;
            }
        };
    }

    // create or open the file
    let file = File::create(filepath.as_ref())?;
    let mut writer = io::BufWriter::new(file);

    // unsigned integer
    uint_mod!(writer, 8);
    uint_mod!(writer, 16);
    uint_mod!(writer, 32);
    uint_mod!(writer, 64);
    uint_mod!(writer, 128);

    // signed integer
    int_mod!(writer, 8);
    int_mod!(writer, 16);
    int_mod!(writer, 32);
    int_mod!(writer, 64);
    int_mod!(writer, 128);

    writer.flush()?;
    Ok(())
}

fn main() {
    // rerun this build script if it has changed
    println!("cargo:rerun-if-changed=build.rs");

    // Get the path to the crate directory
    let crate_dirpath = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR doesn't exist for creusot crate ??"));

    // Get the path to the prelude directory
    let prelude_dirpath = crate_dirpath.join("..").join("prelude");

    // We create the directory if it does not exist
    fs::create_dir_all(&prelude_dirpath).expect("creusot crate build, can't create prelude directory");

    // Create the file name for the prelude dedicated to integers
    let int_prelude_filepath = prelude_dirpath.join("int.coma");

    // create integer prelude
    int_prelude_maker(&int_prelude_filepath).unwrap_or_else(|e| {
        eprintln!("Erreur in int_prelude_maker: {}", e);
        std::process::exit(1); 
    });
}