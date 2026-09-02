// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.
// spell-checker:ignore strftime

#![no_main]
use libfuzzer_sys::fuzz_target;
use uu_date::uumain;

use rand::RngExt;
use rand::SeedableRng;
use rand::rngs::StdRng;
use rand::seq::IndexedRandom;
use std::env;
use std::ffi::OsString;
use std::sync::Once;

use uufuzz::CommandResult;
use uufuzz::{compare_result, generate_and_run_uumain, run_gnu_cmd};

static CMD_PATH: &str = "date";

/// Every invocation pins the date with `-d`: uutils runs in-process, GNU as a child,
/// and a second boundary crossed between the two would show up as a spurious mismatch.
///
/// The years vary on purpose: GNU applies flags to the year sub-field of some
/// composite specifiers, so a same-year set could not observe that (`%-D` is
/// `06/15/24` on 2024 but `03/04/5` on 2005).
const REFERENCE_DATES: &[&str] = &[
    "2024-06-15 07:05:03",
    "2026-12-25 23:59:59",
    "2005-03-04 07:05:03", // %y = 05
    "2001-09-11 08:46:00", // %y = 01
    "2000-02-29 12:00:00", // %y = 00, leap day
    "1905-08-08 08:08:08",
    "2010-01-01 00:00:00", // %y = 10, no leading zero
    "0999-12-31 23:59:59", // three-digit year
    "0009-05-05 05:05:05", // single-digit year
    "0001-01-01 00:00:00",
    "@1700000000", // epoch form
];

/// Specifiers that agree with GNU under every flag and width generated here.
const SPECIFIERS: &[char] = &[
    'A', 'B', 'G', 'H', 'I', 'M', 'S', 'U', 'V', 'W', 'Y', 'a', 'b', 'd', 'e', 'g', 'h', 'j', 'k',
    'l', 'm', 'q', 's', 'u', 'w', 'y',
];

/// Specifiers uutils and GNU already disagree on; generating them would bury new
/// regressions under known bugs. Once a row is fixed, move it into `SPECIFIERS`.
/// Reproduce rows with `TZ=UTC LC_ALL=C gnudate -d <date> +<format>` (GNU 9.7).
///
/// | spec | example                 | uutils            | GNU            | issue |
/// |------|-------------------------|-------------------|----------------|-------|
/// | `%C` | `%C`   on `0001-01-01`  | `0`               | `00`           | none  |
/// | `%c` | `%c`   on `0001-01-01`  | `… 00:00:00 0001` | `… 00:00:00 1` | #11657, #12897, #14351 |
/// | `%D` | `%-D`  on `2005-03-04`  | `03/04/05`        | `03/04/5`      | #11657 |
/// | `%F` | `%0F`  on `0001-01-01`  | `0001-01-01`      | `1-01-01`      | #11657 |
/// | `%N` | `%-N`                   | `0`               | `000000000`    | #12034 |
/// | `%n` | `%2n`                   | `0\n`             | ` \n`          | none  |
/// | `%P` | `%^P`  at 13:00         | `PM`              | `pm`           | #14351 |
/// | `%t` | `%2t`                   | `0\t`             | ` \t`          | none  |
/// | `%z` | `%-z`                   | `+0000`           | `+0`           | none  |
/// | `%+` | `%_12+`                 | `%_12+`           | `       %_12+` | none (#10242) |
///
/// `%R %T %X %r %x` are the rest of #11657: a flag or width applies to the expanded
/// sub-format instead of the expansion as a whole (`%-T` gives `7:05:03` where GNU
/// keeps `07:05:03`).
///
/// `%c %p %P %r %Z` also diverge on the case flags: uutils applies `^`/`#` to the
/// rendered string and lets `^` cancel `#`, where GNU's are per specifier (#14351).
const KNOWN_DIVERGENT: &[char] = &[
    'C', 'D', 'F', 'N', 'P', 'R', 'T', 'X', 'Z', 'c', 'n', 'p', 'r', 't', 'x', 'z', '+',
];

/// The two tables above must stay disjoint.
const _: () = {
    let mut i = 0;
    while i < SPECIFIERS.len() {
        let mut j = 0;
        while j < KNOWN_DIVERGENT.len() {
            assert!(
                SPECIFIERS[i] != KNOWN_DIVERGENT[j],
                "a specifier is listed as both clean and known-divergent"
            );
            j += 1;
        }
        i += 1;
    }
};

/// `+` is excluded like the specifiers above: uutils emits a literal `+` where GNU
/// zero-pads (`%+1d` gives `+5`, GNU gives `5`). #10999 fixed the no-explicit-width
/// half of #10957; this is the remainder.
const FLAGS: &[&str] = &["", "-", "_", "0", "^", "#"];

const LITERALS: &[&str] = &["", " ", "|", "-", "T", "%%", "[", "]"];

/// The pre-existing argument fuzzer (option parsing and the `-d` date-string parser),
/// kept because the differential half below only ever runs `-d <date> +<format>`.
fn fuzz_arguments(data: &[u8]) {
    let fuzz_args: Vec<OsString> = data
        .split(|b| *b == 0)
        .filter_map(|e| std::str::from_utf8(e).ok())
        .map(OsString::from)
        .collect();

    // Skip test cases that would cause the program to read from stdin.
    // These would hang the fuzzer waiting for input.
    for i in 0..fuzz_args.len() {
        if let Some(arg) = fuzz_args.get(i) {
            let arg_bytes = arg.as_encoded_bytes();
            // Skip if -f- or --file=- or combined options like -Rf- (reads dates from stdin)
            if (arg_bytes.first() == Some(&b'-')
                && !arg_bytes.starts_with(b"--")
                && arg_bytes.ends_with(b"f-"))
                || (arg_bytes == b"-f"
                    && fuzz_args
                        .get(i + 1)
                        .map(|a| a.as_encoded_bytes() == b"-")
                        .unwrap_or(false))
                || matches!(arg_bytes, b"-f-" | b"--file=-")
            {
                return;
            }
        }
    }

    // Add program name as first argument (required for proper argument parsing)
    let mut args = vec![OsString::from("date")];
    args.extend(fuzz_args);

    let _ = generate_and_run_uumain(&args, uumain, None);
}

fn generate_format(rng: &mut impl RngExt) -> String {
    let mut out = String::new();
    for _ in 0..rng.random_range(1..=4) {
        out.push_str(LITERALS.choose(rng).unwrap());
        out.push('%');
        // Occasionally emit two flags to exercise conflicting-flag precedence.
        out.push_str(FLAGS.choose(rng).unwrap());
        if rng.random_bool(0.2) {
            out.push_str(FLAGS.choose(rng).unwrap());
        }
        // Widths above 65535 are rejected by uutils while GNU still pads; stay under.
        if rng.random_bool(0.45) {
            out.push_str(&rng.random_range(0..=40).to_string());
        }
        out.push(*SPECIFIERS.choose(rng).unwrap());
        out.push_str(LITERALS.choose(rng).unwrap());
    }
    out
}

/// All randomness derives from libFuzzer's input, so the artifact written on a
/// mismatch replays the exact date and format that failed.
fn fuzz_format_against_gnu(data: &[u8]) {
    let mut seed = [0u8; 32];
    for (dst, src) in seed.iter_mut().zip(data) {
        *dst = *src;
    }
    let mut rng = StdRng::from_seed(seed);
    let date = *REFERENCE_DATES.choose(&mut rng).unwrap();
    // `compare_result` trims both sides, which would hide padding at the very start
    // or end of the output — and padding is most of what these flags do.
    let format = format!("+|{}|", generate_format(&mut rng));

    let args = vec![
        OsString::from("date"),
        OsString::from("-d"),
        OsString::from(date),
        OsString::from(format),
    ];

    let rust_result = generate_and_run_uumain(&args, uumain, None);

    let gnu_result = match run_gnu_cmd(CMD_PATH, &args[1..], false, None) {
        Ok(result) => result,
        Err(error_result) => {
            eprintln!("Failed to run GNU command:");
            eprintln!("Stderr: {}", error_result.stderr);
            eprintln!("Exit Code: {}", error_result.exit_code);
            CommandResult {
                stdout: String::new(),
                stderr: error_result.stderr,
                exit_code: error_result.exit_code,
            }
        }
    };

    compare_result(
        "date",
        &format!("{:?}", &args[1..]),
        None,
        &rust_result,
        &gnu_result,
        false, // Set to true if you want to fail on stderr diff
    );
}

static PIN_ENV: Once = Once::new();

fuzz_target!(|data: &[u8]| {
    // `date` is timezone-sensitive and GNU runs in a separate process, so pin the
    // zone for both sides (`run_gnu_cmd` already pins the child's LC_ALL).
    PIN_ENV.call_once(|| {
        // SAFETY: libFuzzer drives this target single-threaded, and the reader threads
        // uufuzz spawns are not running yet.
        unsafe {
            env::set_var("TZ", "UTC");
            env::set_var("LC_ALL", "C");
        }
        // Refuse to compare against a system `date` that is itself uutils (some
        // distributions ship that); `is_gnu_cmd` panics rather than returning an error.
        let _ = uufuzz::is_gnu_cmd(CMD_PATH);
    });

    // Split the selector byte off instead of reusing it: `-` is odd, so passing the
    // whole slice would hide every option-shaped input from `fuzz_arguments`.
    let Some((&selector, rest)) = data.split_first() else {
        return;
    };
    if selector % 2 == 0 {
        fuzz_arguments(rest);
    } else {
        fuzz_format_against_gnu(rest);
    }
});
