#!/usr/bin/env python3

import os
import sys

def remove_blocks(lines, *, matching_with, opening, closing):
    is_inside_block = False
    depth_block = 0

    for line in lines:
        stripped = line.strip()

        if not is_inside_block and matching_with(stripped):
            is_inside_block = True

            if not opening:
                depth_block = 1

        if is_inside_block:
            if opening:
                depth_block += stripped.count(opening)

            depth_block -= stripped.count(closing)

            if depth_block <= 0:
                is_inside_block = False
                depth_block = 0

            continue

        yield line

def remove_empty_lines(lines):
    yield from (line for line in lines if line.strip())

def remove_inline_comments(lines):
    yield from (line for line in lines if not line.strip().startswith("//"))

def remove_block_comments(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("/*"),
        opening = "",
        closing = "*/"
    )

def remove_test_fn(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("fn test()") or s.startswith("pub fn test()"),
        opening = "{",
        closing = "}",
    )


def remove_rust_annotations(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("#![") or s.startswith("#[allow(") or s.startswith("#[cfg(creusot)]"),
        opening = "[",
        closing = "]"
    )

def remove_creusot_annotations(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("#[erasure"),
        opening = "[",
        closing = "]"
    )

def remove_creusot_use(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("use creusot"),
        opening = "",
        closing = ";",
    )

def remove_creusot_spec(lines):
    yield from remove_blocks(
        lines,
        matching_with = lambda s: s.startswith("mod spec") or s.startswith("pub mod spec") or s.startswith("erase!"),
        opening = "{",
        closing = "}",
    )

def apply_phases(lines, phases):
    result = iter(lines)
    for simplifier in phases:
        result = simplifier(result)

    yield from result


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <file_path>")
        sys.exit(1)

    filename = sys.argv[1]
    basename = os.path.basename(filename)
    filename_nospec = filename.replace(basename, f"nospec/{basename}")

    with open(filename, "r") as file:
        phases = [
            remove_empty_lines,
            remove_inline_comments,
            remove_block_comments,
            remove_test_fn,
            remove_rust_annotations,
        ]

        length = len(list(apply_phases(file, phases)))
        print(f"Number of lines before simplification: {length}")

    with open(filename_nospec, "r") as file:
        phases = [
            remove_empty_lines,
            remove_inline_comments,
            remove_block_comments,
            remove_test_fn,
            remove_rust_annotations,
            remove_creusot_annotations,
            remove_creusot_use,
            remove_creusot_spec,
        ]

        length = len(list(apply_phases(file, phases)))
        print(f"Number of lines after simplification:  {length}")
