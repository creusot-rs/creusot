use clap::Parser;
use git2::{build::CheckoutBuilder, Repository};
use roxmltree::Document;
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

#[derive(Parser, Debug)]
struct Args {
    /// Only check coma files that differ from the provided source in the git history (useful for small PRs)
    #[clap(long = "diff-from")]
    diff_from: Option<String>,
    /// Only run tests which contain this string
    filter: Option<String>,
}

fn main() {
    let args = Args::parse();

    if let Some(from) = &args.diff_from {
        let old = collect_stats_at_rev(from, &args).unwrap();

        let mut stats: Vec<_> = collect_stats(&args)
            .filter_map(|(f, new)| {
                let old = old.get(&f)?;
                if old.time > 0.0 {
                    let d_t = new.time / old.time - 1.;
                    Some((f, old, new, d_t))
                } else {
                    None
                }
            })
            .collect();

        let mean_d_t = stats.iter().map(|s| s.3).sum::<f64>() / (stats.len() as f64);

        stats.sort_by_key(|(_, _, _, c)| (c * 10000.) as i64);

        for (file, old, new, d_t) in stats {
            let file = file.strip_prefix("../creusot/tests").unwrap().parent().unwrap();
            let d_n = new.steps as f64 / old.steps as f64 - 1.;
            println!(
                "{}: t_old={:.2} t_new={:.2} ({:+.1}%) n_old={} n_new={} ({:+.1}%)",
                file.display(),
                old.time,
                new.time,
                d_t * 100.,
                old.steps,
                new.steps,
                d_n * 100.,
            );
        }

        println!("mean change in proof time: {:+.1}%", mean_d_t * 100.)
    } else {
        for (file, stats) in collect_stats(&args) {
            println!(
                "{}: time={:.2} steps={}",
                file.parent().unwrap().display(),
                stats.time,
                stats.steps
            );
        }
    }
}

fn collect_stats_at_rev(rev: &str, args: &Args) -> Result<HashMap<PathBuf, Stats>, git2::Error> {
    let mut repo = Repository::open("..")?;

    let sig = repo.signature()?;
    let stashed = match repo.stash_save2(&sig, None, None) {
        Ok(_) => Ok(true),
        Err(e) if e.code() == git2::ErrorCode::NotFound => Ok(false),
        Err(e) => Err(e),
    }?;

    let rev = repo.revparse_single(rev)?;
    repo.checkout_tree(&rev, None)?;
    drop(rev);

    let old_stats = collect_stats(&args).collect();

    repo.checkout_head(Some(CheckoutBuilder::new().force()))?;
    if stashed {
        repo.stash_pop(0, None)?;
    }

    Ok(old_stats)
}

#[derive(Copy, Clone, Default, Debug)]
struct Stats {
    time: f64,
    steps: u64,
}

fn collect_stats(args: &Args) -> impl Iterator<Item = (PathBuf, Stats)> + '_ {
    let filter = args.filter.clone();
    glob::glob("../creusot/tests/**/why3session.xml")
        .unwrap()
        .flatten()
        .filter(move |f| match (&filter, f.to_str()) {
            (Some(filter), Some(f)) => f.contains(filter),
            _ => true,
        })
        .map(|f| {
            let stats = stats_for_session(&f);
            (f, stats)
        })
}

fn stats_for_session(sess: &Path) -> Stats {
    let session = std::fs::read_to_string(sess).unwrap();
    let doc = Document::parse(&session).unwrap();
    doc.descendants()
        .filter(|n| {
            n.is_element()
                && n.tag_name().name() == "result"
                && n.attribute("status") == Some("valid")
        })
        .fold(Stats::default(), |mut stats, n| {
            stats.time += n.attribute("time").unwrap().parse::<f64>().unwrap();
            stats.steps += n.attribute("steps").and_then(|a| a.parse::<u64>().ok()).unwrap_or(0);
            stats
        })
}
