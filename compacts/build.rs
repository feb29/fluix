use std::{env, fs, io, io::Write, path::Path};

fn gentab(size: usize) -> Vec<Vec<u128>> {
    let mut table = vec![vec![0u128; size]; size];
    for k in 0..size {
        table[k][k] = 1; // initialize diagonal
        table[0][k] = 0; // initialize first row
        table[k][0] = 1; // initialize first col
    }
    for i in 1..size {
        for j in 1..size {
            table[i][j] = table[i - 1][j - 1] + table[i - 1][j];
        }
    }
    table
}

fn rrr_table<P: AsRef<Path>>(path: P, arr_ty: &str, n: usize) -> io::Result<()> {
    let dir = env::var("OUT_DIR").unwrap();
    let mut file = fs::File::create(Path::new(&dir).join(path))?;
    writeln!(
        file,
        r#"#[allow(clippy::unreadable_literal)]
pub static TABLE: {} = {:#?};
"#,
        arr_ty,
        gentab(n)
    )
}

fn main() -> io::Result<()> {
    rrr_table("table.rs", "[[u128;  127]; 127]", 127)
}
