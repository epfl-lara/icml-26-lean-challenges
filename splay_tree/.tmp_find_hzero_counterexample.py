"""Find a concrete counterexample to Codex's `hzero_after_lower`:
   actualResetFirstLowerPairGapPotential Y q init (done ++ [i]) future = 0
which Codex assumes for ALL lower accesses. It should FAIL in the descent case
(a future lower key < current Y i). We want the smallest explicit instance.
"""
from __future__ import annotations
import importlib.util
from itertools import product
from pathlib import Path

BASE = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("b", BASE)
assert SPEC and SPEC.loader
base = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl, splay, N, E = base.path_len, base.splay, base.N, base.E


def keys(t):
    return [] if not t else keys(t[0]) + [t[1]] + keys(t[2])


def splay_after(t, seq):
    for x in seq:
        t = splay(t, x)
    return t


def reset_after(t, seq, q):
    for x in seq:
        if x < q:
            t = splay(splay(t, x), q)
    return t


def gap_after_lower(init, q, done, i, future):
    """actualResetFirstLowerPairGapPotential at state (done++[i]) over future."""
    a = splay_after(init, done + [i])
    r = reset_after(init, done + [i], q)
    for z in future:
        if z < q:
            return max(0, spl(a, z) + spl(splay(a, z), q) - spl(a, q)
                       - spl(r, z) - spl(splay(r, z), q))
    return 0


found = []
for q in range(2, 7):
    for L in base.trees(0, q):
        init = N(L, q, E)                  # rooted at q, keys 0..q
        for length in range(2, 6):
            for seq in product(range(q), repeat=length):
                s = list(seq)
                if not base.avoids231(s):
                    continue
                for pos in range(0, length - 1):      # i = s[pos], need a future
                    done, i, future = s[:pos], s[pos], s[pos + 1:]
                    if i >= q:
                        continue
                    g = gap_after_lower(init, q, done, i, future)
                    if g > 0:
                        found.append((g, q, keys(L), s, pos))
    if found:
        break

found.sort(key=lambda t: (t[1], len(t[3]), t[4], -t[0]))
print(f"counterexamples found: {len(found)}")
for g, q, lkeys, s, pos in found[:8]:
    print(f"  q={q} leftKeys={lkeys} seq={s} pos={pos} done={s[:pos]} i={s[pos]} future={s[pos+1:]} -> gap={g}")
if found:
    g, q, lkeys, s, pos = found[0]
    print(f"\nMINIMAL: q={q} leftKeys={lkeys} seq={s} pos={pos}")
    fut=s[pos+1:]; print(f"  done={s[:pos]} i(val)={s[pos]} future(vals)={fut}; first future lower {next(z for z in fut if z<q)} vs i {s[pos]} -> gap={g}>0")
