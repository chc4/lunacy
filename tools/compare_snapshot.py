#!/usr/bin/env python3
"""Compare a screen snapshot with a reference image, pixel by pixel: how many
differ, and where the first does. With `--diff`, an image of the two side by
side with the differing pixels between them in red. Exits 1 if any differ.

    compare_snapshot.py <actual> <expected> [--diff out.png]
"""
import argparse
import sys

from PIL import Image


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("actual")
    parser.add_argument("expected")
    parser.add_argument("--diff", help="where to write the side-by-side image")
    args = parser.parse_args()

    actual = Image.open(args.actual).convert("RGB")
    expected = Image.open(args.expected).convert("RGB")
    if actual.size != expected.size:
        print(f"{args.actual}: size {actual.size}, expected {expected.size}")
        sys.exit(1)

    width, height = actual.size
    a, e = actual.load(), expected.load()
    differing = [(x, y) for y in range(height) for x in range(width) if a[x, y] != e[x, y]]
    if args.diff:
        out = Image.new("RGB", (width * 3, height), "white")
        out.paste(expected, (0, 0))
        out.paste(actual, (width * 2, 0))
        for x, y in differing:
            out.putpixel((width + x, y), (255, 0, 0))
        out.save(args.diff)
    if differing:
        x, y = differing[0]
        print(f"{args.actual}: {len(differing)} of {width * height} pixels differ, the first at ({x}, {y}): {a[x, y]}, expected {e[x, y]}")
        sys.exit(1)
    print(f"{args.actual}: matches {args.expected}")


if __name__ == "__main__":
    main()
