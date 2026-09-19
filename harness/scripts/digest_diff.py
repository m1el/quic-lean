#!/usr/bin/env python3
"""Join two DIFF_DIGEST files (endpoint_diff.c) made from the same inputs.

    DIFF_DIGEST=out/ngtcp2.digest ./out/endpoint_diff -runs=0 corpus/conn_trace
    DIFF_DIGEST=out/quiche.digest ./out/quiche_diff   -runs=0 corpus/conn_trace
    harness/scripts/digest_diff.py out/ngtcp2.digest out/quiche.digest

Every input is one run of steps in each file.  Runs are compared step by step up
to the first difference (after it the two connections are in different states,
so later differences are consequences).  The first difference is classified:

  latitude   both implementations were accepted by the model and did different
             things: genuine freedom in the text, or a rule the model lacks.
             Neither pairwise diff reports these -- they are why this exists.
  A-only /   one implementation was a MISMATCH for the model and the other was
  B-only     accepted: the first is the suspect.
  both       both were MISMATCHes: the model is the suspect.

A run that is shorter in one file (that side closed, or skipped a step) is
reported as `length` only if no difference came first.
"""
import collections
import sys


def load(path):
    runs = collections.OrderedDict()
    with open(path) as f:
        for line in f:
            p = line.split()
            if len(p) < 6:
                continue
            inp, _step, ev, res, lean, cbs = p[0], p[1], p[2], p[3], p[4], p[5]
            runs.setdefault(inp, []).append((ev, res, lean, cbs))
    return runs


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    a, b = load(sys.argv[1]), load(sys.argv[2])
    common = [k for k in a if k in b]
    kinds = collections.Counter()
    sigs = collections.defaultdict(list)
    same = 0
    for k in common:
        ra, rb = a[k], b[k]
        first = None
        for i, (x, y) in enumerate(zip(ra, rb)):
            if x[0] != y[0]:
                first = (i, "desync", x, y)  # different event: step lists diverged
                break
            if (x[1], x[3]) != (y[1], y[3]) or x[2] != y[2]:
                first = (i, None, x, y)
                break
        if first is None:
            if len(ra) != len(rb):
                kinds["length"] += 1
            else:
                same += 1
            continue
        i, kind, x, y = first
        if kind is None:
            ma, mb = x[2] == "MISMATCH", y[2] == "MISMATCH"
            if (x[1], x[3]) == (y[1], y[3]):
                kind = "model-only"  # same behaviour, the model judged it differently
            elif ma and mb:
                kind = "both"
            elif ma:
                kind = "A-only"
            elif mb:
                kind = "B-only"
            else:
                kind = "latitude"
        kinds[kind] += 1
        sig = "%-10s %-8s A: %-10s %-28s B: %-10s %s" % (kind, x[0], x[1], x[3], y[1], y[3])
        sigs[sig].append((k, i))

    print("inputs: A=%d B=%d common=%d identical=%d" % (len(a), len(b), len(common), same))
    for kind, n in kinds.most_common():
        print("  %-10s %d" % (kind, n))
    print()
    for sig, where in sorted(sigs.items(), key=lambda kv: -len(kv[1])):
        k, i = where[0]
        print("x%-5d %s   e.g. input %s step %d" % (len(where), sig, k, i))


if __name__ == "__main__":
    main()
