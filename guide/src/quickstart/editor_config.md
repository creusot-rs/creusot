From the root of your project, write the following in the `.vscode/settings.json` file:
```json
{
  "rust-analyzer.check.overrideCommand": [
    "cargo",
    "creusot",
    "--",
    "--message-format=json"
  ]
}
```

For other editors, see <https://rust-analyzer.github.io/book/other_editors.html> to add the above option to your configuration.

Note that you will probably want to enable this option _only_ in projects that use creusot.
