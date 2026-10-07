#!/usr/bin/env python3
"""Read-only conservative review inventory; never applies source deletions."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)\s*$', re.M)
TOKEN = re.compile(r"[\w']+", re.UNICODE)
SUPPORT = re.compile(r'(?m)^\s*(?:(?:local|scoped|public|private|noncomputable|unsafe)\s+)*(?:instance|attribute|syntax|macro|macro_rules|elab|elab_rules|initialize|builtin_initialize|notation|infix[lr]?|prefix|postfix|export|example|set_option|register_option)\b|@\[')
DECL = re.compile(r'^\s*(?:(?:public|private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev)\s+([\w.\']+)\b')


def mask_comments_strings(s):
    # Preserve offsets/newlines; nested Lean comments and escaped strings.
    out = list(s)
    i, depth, string = 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2; continue
            if s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2; continue
            if s[i] != '\n': out[i] = ' '
        elif string:
            if s[i] == '\\' and i + 1 < len(s):
                out[i] = out[i+1] = ' '; i += 2; continue
            if s[i] == '"': string = False
            if s[i] != '\n': out[i] = ' '
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2; continue
        elif s.startswith('--', i):
            end = s.find('\n', i)
            if end < 0: end = len(s)
            out[i:end] = ' ' * (end-i); i = end; continue
        elif s[i] == '"':
            string = True; out[i] = ' '
        i += 1
    return ''.join(out)


def analyze(root, trace, expected):
    rows, deadmods, axioms = defaultdict(list), set(), set()
    complete = False
    for line in trace.read_text().splitlines():
        bits = line.split('|')
        if bits[0] in ('LIVE', 'DEAD') and len(bits) == 5:
            tag, mod, name, a, b = bits
            rows[mod].append(dict(live=tag == 'LIVE', name=name,
                                 start=None if a == '?' else int(a),
                                 end=None if b == '?' else int(b)))
        elif bits[0] == 'DEADMOD' and len(bits) == 2: deadmods.add(bits[1])
        elif bits[0] == 'AXIOM' and len(bits) == 2: axioms.add(bits[1])
        elif line.startswith('# project constants:'): complete = True
    if not complete: raise ValueError('Trace lacks completion summary; refusing incomplete inventory')
    live = {r['name'] for rr in rows.values() for r in rr if r['live']}
    if expected not in live: raise ValueError(f'Expected root is not LIVE: {expected}')
    unexpected = axioms - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected: raise ValueError(f'Unexpected axioms: {sorted(unexpected)}')
    live_ancestors = {'.'.join(n.split('.')[:i]) for n in live for i in range(1, len(n.split('.')) + 1)}
    sources, raw, imports, usages = {}, {}, {}, defaultdict(set)
    for path in sorted((root / 'Wikipedia').rglob('*.lean')):
        mod = '.'.join(path.relative_to(root).with_suffix('').parts)
        raw[mod] = path.read_text()
        sources[mod] = mask_comments_strings(raw[mod])
        imports[mod] = set(IMPORT.findall(sources[mod]))
        for n, line in enumerate(sources[mod].splitlines(), 1):
            for token in set(TOKEN.findall(line)): usages[token].add((mod, n))
    incoming = defaultdict(set)
    for mod, deps in imports.items():
        for dep in deps: incoming[dep].add(mod)
    module_reviews, decl_reviews, protected = [], [], defaultdict(int)
    for mod in sorted(deadmods):
        if mod not in sources: continue
        blockers = []
        support_text = re.sub(r'@\[expose\]\s+public\s+section', '', sources[mod])
        if SUPPORT.search(support_text): blockers.append('elaboration-support-or-attributes')
        if not rows[mod]: blockers.append('no-traced-declarations/barrel')
        if any(r['live'] for r in rows[mod]): blockers.append('inconsistent-live-module')
        outside = sorted(incoming[mod] - deadmods)
        module_reviews.append(dict(module=mod, lines=len(raw[mod].splitlines()),
            blockers=blockers, incoming_from_retained=outside,
            direct_imports=sorted(imports[mod]),
            classification='manual-support-review' if blockers else 'module-batch-review',
            sha256=hashlib.sha256(raw[mod].encode()).hexdigest()))
    for mod, rr in rows.items():
        if mod not in sources: continue
        lines = sources[mod].splitlines()
        intervals = defaultdict(list)
        for r in rr:
            if r['start'] is not None: intervals[(r['start'], r['end'])].append(r)
        for (a, b), group in sorted(intervals.items()):
            names = [r['name'] for r in group]
            if a < 1 or b > len(lines) or b < a:
                protected['invalid-range'] += 1; continue
            if any(r['live'] and (r['start'] is not None and a <= r['end'] and r['start'] <= b)
                   for r in rr):
                protected['live-overlap'] += 1; continue
            # A rangeless generated descendant still protects its containing command.
            if any(x in live_ancestors for x in names):
                protected['live-generated-descendant'] += 1; continue
            body = '\n'.join(lines[a-1:b])
            m = DECL.match(body)
            if not m or SUPPORT.search(body):
                protected['non-simple-command-or-support'] += 1; continue
            if sum(bool(DECL.match(line)) for line in lines[a-1:b]) != 1:
                protected['multiple-command-range'] += 1; continue
            token = m[2].split('.')[-1]
            references = sorted((f, n) for f, n in usages[token] if f != mod or not a <= n <= b)
            if references:
                protected['textual-client'] += 1; continue
            # Wrappers/attributes can precede Lean's declaration range. Never consume them blindly.
            prev = a - 2
            while prev >= 0 and not lines[prev].strip(): prev -= 1
            if prev >= 0 and (lines[prev].strip().endswith(' in') or '@[' in lines[prev]):
                protected['preceding-wrapper-or-attribute'] += 1; continue
            if any(r['start'] is not None and (a <= r['end'] and r['start'] <= b)
                   and not (a <= r['start'] and r['end'] <= b) for r in rr):
                protected['partial-range-overlap'] += 1; continue
            decl_reviews.append(dict(module=mod, start=a, end=b, names=names,
                kind=m[1], lines=b-a+1, classification='isolated-command-manual-review',
                source_excerpt='\n'.join(raw[mod].splitlines()[a-1:min(b, a+3)]),
                sha256=hashlib.sha256(raw[mod].encode()).hexdigest()))
    return dict(trace=str(trace), expected_root=expected, axioms=sorted(axioms),
        warning='Heuristic review inventory only. No candidate is certified safe to delete. '
                'Ranges have no columns; verify full command boundaries, source freshness, '
                'elaboration effects and rebuild the exact root after bounded batches.',
        protected_counts=dict(protected), modules=sorted(module_reviews,key=lambda x:-x['lines']),
        declarations=sorted(decl_reviews,key=lambda x:-x['lines']))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('trace', type=Path)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--expected-root', default='NoExoticSixSphere.noExoticSixSpheres')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    report = analyze(a.root.resolve(), a.trace.resolve(), a.expected_root)
    a.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(module_reviews=len(report['modules']),
                          isolated_declaration_reviews=len(report['declarations']),
                          protected_counts=report['protected_counts'])))

if __name__ == '__main__': main()
