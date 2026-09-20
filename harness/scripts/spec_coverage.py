#!/usr/bin/env python3
"""Which rows of the Spec files' coverage tables does a corpus replay exercise?

    harness/scripts/spec_coverage.py out/cov_fn_init.json \\
        ngtcp2=out/cov_fn_ngtcp2.json cq=out/cov_fn_cq.json gq=out/cov_fn_gq.json

Compare saved tables with:
    harness/scripts/spec_coverage.py --diff old.tsv new.tsv

Each JSON maps a C function name to [execution count, source file], made from
`llvm-cov export -skip-expansions` of a harness built with the Lean-emitted C
under -fprofile-instr-generate (PLAN.md section 4n).  The first file is the
profile of a run with no input at all: Lean evaluates closed terms (the
Examples, mostly) when a module is initialised, and that alone executes
thousands of model functions.  A function counts as *exercised* only if the
replay ran it more often than initialisation did.

A coverage-table row is `| §x.y (line) | "sentence" | encoded as |`.  The
back-quoted identifiers of the third column are resolved against the
namespaces open at that line, mangled the way Lean mangles them, and looked up
among the C functions (the definition itself, its `_redArg`/`_boxed`/`_lam`
workers, its match splitters and its specialisations).  A `Prop` has no code;
for `MaySend` the Bool twin `maySend` and `instDecidableMaySend` are tried.

The Spec is relational: `Step.foo` is a constructor of an inductive `Prop`
and has no code.  What runs is the component's `outcomes`, proved equivalent to
`Step`, and the *guards* the constructor's hypotheses name (`failCase s p =
.revert`).  A `Step.foo` identifier is therefore resolved to the definitions
its constructor mentions; if none has code, to `outcomes` ("via outcomes": only
says the component was stepped at all).  This is function granularity -- it
says `failCase` ran, not that it answered `.revert`.

Known blind spot: a definition the Lean compiler inlined everywhere has a C
function nobody calls, and reads as not exercised.  All forms of a name are
therefore pooled (the definition, its Bool twin, its `instDec*` instance).

A row is
    executable   at least one identifier resolved to code
    exercised    at least one of those was run by the replay
    no-code      identifiers exist but none has code (theorems, types, Props
                 without a decision procedure in the binary)
    unnamed      the third column names no identifier (prose: out of scope,
                 informative, ...)
"""
import collections
import glob
import json
import re
import sys

ROW = re.compile(r'^\|\s*(§[^|]*?)\|(.*)\|([^|]*)\|\s*$')
NORM = re.compile(r'\b(MUST NOT|MUST|SHOULD NOT|SHOULD|MAY|REQUIRED|RECOMMENDED)\b')


def mangle(name):
    return '_'.join(c.replace('_', '__') for c in name.split('.'))


def load(path):
    return {k: v[0] for k, v in json.load(open(path)).items()}


class Index:
    """C functions by the mangled Lean definition they belong to."""

    def __init__(self, names):
        self.by_owner = collections.defaultdict(list)
        # Longest-prefix lookup is too loose (`maySend` vs `maySendPacket` is
        # fine, `Ranges` vs `Ranges_mem` is not), so owners are recovered by
        # stripping the known worker suffixes instead.
        for n in names:
            base = n
            if base.startswith('lp_QuicModel_'):
                base = base[len('lp_QuicModel_'):]
            m = re.match(r'__private_.*?_0__(.*)$', base)
            if m:
                base = m.group(1)
            m = re.search(r'___at___00(.*?)_spec__\d+', base)
            if m:
                base = m.group(1)
            base = re.sub(r'(___boxed|___redArg|___lam__\d+|___lambda__\d+|___closed__\d+'
                          r'|_match__\d+_splitter|___elam__\d+|___override|___aux__\d+)+$', '', base)
            base = re.sub(r'(___boxed|___redArg|___lam__\d+|_match__\d+_splitter|___aux__\d+)+$', '', base)
            self.by_owner[base].append(n)

    def funcs(self, lean_name):
        return self.by_owner.get(mangle(lean_name), [])


def candidates(ident, namespaces):
    """Full names an identifier of a table cell may stand for."""
    out = []
    ident = ident.strip().lstrip('@')
    if not re.match(r'^[A-Za-z_][\w.\']*$', ident):
        return out
    spaces = []
    for ns in namespaces:
        parts = ns.split('.')
        for i in range(len(parts), 0, -1):
            spaces.append('.'.join(parts[:i]))
    spaces += ['Quic.Spec', 'Quic', '']
    seen = set()
    for ns in spaces:
        full = (ns + '.' if ns else '') + ident
        if full in seen:
            continue
        seen.add(full)
        out.append(full)
        head, _, last = full.rpartition('.')
        pre = head + '.' if head else ''
        if last[:1].isupper():            # Prop -> its Bool twin / instance
            out.append(pre + last[0].lower() + last[1:])
            out.append(pre + 'instDecidable' + last)
            out.append(pre + 'instDec' + last)
    return out


def rows(path):
    stack, open_ns = [], []
    for ln, line in enumerate(open(path, encoding='utf-8'), 1):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m.group(1))
        elif re.match(r'^end\s+\S+', line) and stack:
            stack.pop()
        m = ROW.match(line.rstrip('\n'))
        if m:
            yield ln, m.group(1).strip(), m.group(2), m.group(3), '.'.join(stack)


def file_namespaces(path):
    """Every namespace a file opens: a table usually sits in the module
    docstring, outside all of them."""
    ns, stack = [], []
    for line in open(path, encoding='utf-8'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m.group(1))
            ns.append('.'.join(stack))
        elif re.match(r'^end\s+\S+', line) and stack:
            stack.pop()
    return ns


def step_constructors(paths):
    """constructor name -> identifiers its declaration mentions, for every
    `inductive Step` (or `... .Step`) of a component."""
    out = {}
    for path in paths:
        lines = open(path, encoding='utf-8').read().split('\n')
        i = 0
        while i < len(lines):
            if re.match(r'^inductive\s+\S*Step\b', lines[i]):
                i += 1
                cur = None
                while i < len(lines) and (lines[i].startswith(' ') or not lines[i].strip()):
                    m = re.match(r'^\s+\|\s+([A-Za-z_][\w\']*)', lines[i])
                    if m:
                        cur = m.group(1)
                        out.setdefault(cur, set())
                    if cur:
                        out[cur].update(re.findall(r"[A-Za-z_][\w.']*", lines[i]))
                    i += 1
            else:
                i += 1
    return out


def diff_rows(old_path, new_path):
    """Compare requirement identities, ignoring Lean source line-number drift."""
    def rows(path):
        result = {}
        with open(path) as f:
            for line in f:
                fields = line.rstrip('\n').split('\t')
                if len(fields) != 7:
                    raise ValueError(f'{path}: expected seven TSV fields')
                component, source, _, ref, state, sentence, _ = fields
                key = (component, source, ref, sentence)
                if key in result:
                    raise ValueError(f'{path}: duplicate requirement identity: {key}')
                result[key] = state
        return result
    old, new = rows(old_path), rows(new_path)
    changed = 0
    for key in sorted(old.keys() | new.keys()):
        before, after = old.get(key, 'absent'), new.get(key, 'absent')
        if before != after:
            changed += 1
            print(f'{key[0]} {key[2]}: {before} -> {after}')
    print(f'{changed} requirement coverage statuses changed')


def main():
    if len(sys.argv) == 4 and sys.argv[1] == '--diff':
        diff_rows(sys.argv[2], sys.argv[3])
        return
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    init = load(sys.argv[1])
    engines = collections.OrderedDict()
    for a in sys.argv[2:]:
        k, _, p = a.partition('=')
        engines[k] = load(p)
    idx = Index(init.keys())

    def ran(fn, prof):
        return prof.get(fn, 0) > init.get(fn, 0)

    comp = collections.OrderedDict()
    detail = []
    paths = sorted(set(glob.glob('QuicModel/Spec/**/*.lean', recursive=True)))
    by_comp = collections.defaultdict(list)
    for path in paths:
        by_comp[path.split('/')[2].replace('.lean', '')].append(path)
    for component, cpaths in by_comp.items():
        nss = []
        for path in cpaths:
            for n in file_namespaces(path):
                if n not in nss:
                    nss.append(n)
        ctors = step_constructors(cpaths)

        def resolve(ident, here):
            # All spellings under the first namespace that yields any code.
            cands = candidates(ident, ([here] if here else []) + nss)
            for i, full in enumerate(cands):
                if idx.funcs(full):
                    head = full.rpartition('.')[0]
                    out = []
                    for other in cands:
                        if other.rpartition('.')[0] == head:
                            out += idx.funcs(other)
                    return out
            return []

        for path in cpaths:
            for ln, ref, sentence, enc, here in rows(path):
                c = comp.setdefault(component, collections.Counter())
                c['rows'] += 1
                if not NORM.search(sentence):
                    continue
                c['norm'] += 1
                idents = re.findall(r'`([^`]+)`', enc)
                direct, guards, via_out = [], [], []
                for ident in idents:
                    f = resolve(ident, here)
                    if f:
                        direct += f
                        continue
                    m = re.match(r'^(?:\w+\.)*Step\.([A-Za-z_][\w\']*)$', ident.strip())
                    if m and m.group(1) in ctors:
                        g = []
                        for tok in ctors[m.group(1)]:
                            if tok in ('s', 'Step', 'State', 'Event', 'Out', m.group(1)):
                                continue
                            g += resolve(tok, here)
                        if g:
                            guards += g
                        else:
                            via_out += resolve('outcomes', here)
                fns = direct or guards or via_out
                kind = 'direct' if direct else 'guard' if guards else 'outcomes' if via_out else ''
                if not idents:
                    c['unnamed'] += 1
                    state = 'unnamed'
                elif not fns:
                    c['nocode'] += 1
                    state = 'no-code'
                else:
                    c['exec'] += 1
                    c['k_' + kind] += 1
                    hit = {k: any(ran(fn, p) for fn in fns) for k, p in engines.items()}
                    for k, v in hit.items():
                        c['hit_' + k] += v
                    anyhit = any(hit.values())
                    c['hit_any'] += anyhit
                    state = ('exercised' if anyhit else 'NOT exercised') + ' (' + kind + ')'
                detail.append((component, path, ln, ref, state, sentence.strip()[:110],
                               ', '.join(idents)[:80]))

    eng = list(engines)
    hdr = ['component', 'norm.rows', 'unnamed', 'no-code', 'executable', 'direct/guard/outcomes'] + eng + ['any']
    print('| ' + ' | '.join(hdr) + ' |')
    print('|' + '---|' * len(hdr))
    tot = collections.Counter()
    for k, c in sorted(comp.items(), key=lambda kv: -kv[1]['norm']):
        if not c['norm']:
            continue
        tot.update(c)
        print('| ' + ' | '.join(
            [k, str(c['norm']), str(c['unnamed']), str(c['nocode']), str(c['exec']), '%d/%d/%d' % (c['k_direct'], c['k_guard'], c['k_outcomes'])] +
            [str(c['hit_' + e]) for e in eng] + [str(c['hit_any'])]) + ' |')
    c = tot
    print('| ' + ' | '.join(
        ['**total**', str(c['norm']), str(c['unnamed']), str(c['nocode']), str(c['exec']), '%d/%d/%d' % (c['k_direct'], c['k_guard'], c['k_outcomes'])] +
        [str(c['hit_' + e]) for e in eng] + [str(c['hit_any'])]) + ' |')

    with open('out/spec_coverage_rows.tsv', 'w') as f:
        for d in detail:
            f.write('\t'.join(str(x) for x in d) + '\n')
    print('\nper-row detail: out/spec_coverage_rows.tsv', file=sys.stderr)


if __name__ == '__main__':
    main()
