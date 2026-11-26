"""Summarize the `deep:` log of recaman_fast --watch B.

Prints, for each decade of the step number, how many zigzags started on a number below B and
how many numbers below B they filled, then lists the fills after a given step.
"""
import re
import sys

path = sys.argv[1]
after = float(sys.argv[2]) if len(sys.argv) > 2 else 1e15
pat = re.compile(r"deep: step (\d+) lands on (\d+) \((\w+)\), fills (\d+)\.\.(\d+); "
                 r"came from zigzag at (-?\d+)\*t([+-]\d+)")
per_decade = {}
late = []
for line in open(path):
    m = pat.match(line)
    if not m:
        continue
    step, x, how, lo, hi, L, off = m.groups()
    step, x, lo, hi = int(step), int(x), int(lo), int(hi)
    d = len(str(step)) - 1
    zz, filled = per_decade.get(d, (0, 0))
    per_decade[d] = (zz + 1, filled + (hi - lo + 1))
    if step >= after:
        late.append((step, x, how, lo, hi, int(L), int(off)))

print("decade  deep zigzags  numbers filled")
for d in sorted(per_decade):
    zz, filled = per_decade[d]
    print(f"1e{d:<3}  {zz:12d}  {filled:14d}")
print(f"\nfills below the bound after step {after:.0e}:")
for step, x, how, lo, hi, L, off in late:
    print(f"  step {step:.4e}: {lo}..{hi} (landed on {x} by {how}, from zigzag at {L}*t{off:+d})")
