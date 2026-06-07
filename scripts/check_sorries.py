#!/usr/bin/env python3
"""Report the number of real `sorry`s in the project (informational only).

Counts term/tactic-position `sorry`s while ignoring Lean comments and string literals, so docstrings narrating proof plans do not inflate the count. This is
still a visibility tool, not a build gate: correctness of the mathematical
surface is checked separately by Lean builds and `#print axioms` probes.
"""
import pathlib

TOKEN = "sorry"


def lean_code_chars(text: str) -> str:
    """Return Lean source with comments and literals replaced by spaces.

    This is intentionally a small scanner rather than a regex: Lean block
    comments nest, and `--` / `/-` can occur inside string literals.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    escape = False

    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if block_depth:
            if c == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue

        if in_string:
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                in_string = False
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue


        if c == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if c == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(c)
        i += 1

    return "".join(out)


def is_ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'"


def count_sorries(text: str) -> int:
    code = lean_code_chars(text)
    count = 0
    start = 0
    while True:
        idx = code.find(TOKEN, start)
        if idx == -1:
            return count
        before = code[idx - 1] if idx else ""
        after_idx = idx + len(TOKEN)
        after = code[after_idx] if after_idx < len(code) else ""
        if not is_ident_char(before) and not is_ident_char(after):
            count += 1
        start = after_idx


def main() -> None:
    root = pathlib.Path(__file__).resolve().parent.parent
    total = 0
    per_file = []
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        n = count_sorries(path.read_text(encoding="utf-8"))
        if n:
            per_file.append((n, str(path.relative_to(root))))
            total += n

    print(f"Term-position sorries: {total}")
    for n, f in sorted(per_file, reverse=True):
        print(f"  {n:3d}  {f}")


if __name__ == "__main__":
    main()
