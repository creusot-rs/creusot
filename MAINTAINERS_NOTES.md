# Notes for maintainers

## Release instructions

To make a release, you must be added as an owner of the relevant crates to publish on crates.io
(`why3`, `pearlite-syn`, `creusot-std-proc`, `creusot-std`). Ask the current owners to add you
(listed on https://crates.io/crates/creusot-std).

Install the `cargo-release` tool, which automates various tasks:

```
cargo install cargo-release
```

1. `git fetch; git checkout origin/master -b release` to make sure you're starting from `master` and make a new branch `release`.
2. Add a list of changes under "Unreleased" in `CHANGELOG.md`. Free style. Suggested approach: list merged PRs, group by themes, write up summaries or highlight important features.
    The following script can be a useful start, converting the git log to a markdown list of links:

    ```
    PREV_VERSION=v0.10.0
    git log $PREV_VERSION..master --pretty=format:'%s'|grep "(#[0-9]*)$"|sed 's_\s*\(.*\S\)\s*(#\([0-9]*\))_- \[\1\](https://github.com/creusot-rs/creusot/pull/\2)_'
    ```

3. (This step is not reversible!) `cargo release --no-tag --no-push X.Y.Z --execute` (where `X.Y.Z` is the new version number). This will:

  a. Bump versions in `Cargo.toml` and `CHANGELOG.md`.
  b. Commit those changes.
  c. Publish the publishable packages on crates.io.
     (Note: CI will need those packages to be published, that's why this step must come before opening the PR.)

4. `git push origin release`, open a PR. Merge it ASAP.
5. `git checkout master; git pull`
6. `git tag vX.Y.Z; git push origin vX.Y.Z` (the tags looks better this way IMO, but it's also OK to remove the `--no-tag` option from `cargo release` above)
7. [Make the release on Github.](https://github.com/creusot-rs/creusot/releases/new)
8. Bump the version to `X.{Y+1}.0-dev` (next prerelease version) in preparation for the next cycle.

  ```shell
  cargo release version 0.{Y+1}.0-dev --execute
  git add -u
  git commit -m "Bump to version 0.{Y+1}.0-dev"
  ```

  Why: the `-dev` prerelease suffix lets `cargo-creusot` tell the difference from the released
  version on crates.io and remind you to do a `cargo creusot init` to update dependencies
  in `Cargo.toml` (or you can run Creusot with `cargo creusot --no-check-version` if you really want to use the released version but it will likely not work at the current pace of changes).

## The creusot.rs domain

- https://creusot.rs, source: https://github.com/creusot-rs/creusot-rs.github.io

  + There is a Github Actions script that automatically synchronizes the version number
    with the creusot-rs/creusot repository on the first of every month.
    Thus the intended workflow is to make a release near the end of every month (we don't
    always manage to do that and that's okay, just bump the version by hand).
    
    * This script needs an up-to-date Github token, which must be renewed every year
      (Github doesn't allow setting a longer expiration time).

        1. Generate a token (see instructions below, under the Creusot User Guide,
           except that the repository here will be creusot-rs/creusot-rs.github.io)

        2. Once you have the token, paste it here:

          1. Go to https://github.com/creusot-rs/creusot-rs.github.io/settings/environments
          2. Click on "bump"
          3. Edit `GH_TOKEN` and paste your token there
          4. You can also update the author of the commit made by the script if you want

- https://guide.creusot.rs (Creusot User Guide), source: the Creusot repo, `guide/` directory,
  but it is deployed by scripts from https://github.com/creusot-rs/guide (can't serve two sites with their own subdomains from a single repo).

  + The guide deploy job is triggered by the master branch of the creusot-rs/creusot repository.
    It also needs a Github token.

    1. Generate a token (it is tied to a user's account)

      1. Go to https://github.com/settings/personal-access-tokens
        If you already have a token for this purpose, you can regenerate it directly and
        skip the following instructions.
      2. Click on "Generate new token", authenticate
      3. Pick a title (what the token is for), and as "Resource owner" select creusot-rs, expiration 366 days
      4. Pick "Only select repositories", and select creusot-rs/guide
      5. Click "Add permissions", select "Contents", then "Access: Read and write"
      6. "Generate token", copy it.

    2. Once you have the token, paste it here:

      1. Go to https://github.com/creusot-rs/creusot/settings/environments
      2. Click on "deploy guide"
      3. Edit `GH_TOKEN` and paste your token there

- https://doc.creusot.rs/creusot_std (API doc), source: https://github.com/creusot, deployed from that same repository (unlike the Guide)
- https://devlog.creusot.rs, source: https://github.com/creusot-rs/devlog
