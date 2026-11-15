#!/usr/bin/env python3
"""Write GwH34/Cert.lean from CaDiCaL's LRAT refutation of the any-colour CNF for (3, 4) on [1, 53].

The CNF is the one of Quantavane's gw_eq.py 53 4 0 (11 Nov 2026; file cnf/gw_any_53_l4.cnf of
gw/certificates.tar.xz in the public data repository arhancanli/quantavane-gw-data): for the points
1..53 (positions 0..52), a variable e(i, j) for each pair i < j says that the two points have the
same colour; clauses, in order: the three transitivity clauses of each triple i < j < k
(itertools.combinations order), then, for each first position a and difference d, the rainbow clause
e(a, a+d) | e(a+d, a+2d) | e(a, a+2d) of each 3-term progression and the clause
-e(a, a+d) | -e(a+d, a+2d) | -e(a+2d, a+3d) of each 4-term progression. pysat's IDPool numbers the
variables in the order of their first use, which this script replays.

This script rebuilds the CNF in that order, checks its SHA-256 against the refuted file, gives every
clause a descriptor from which GwH34.descCls recomputes it in Lean (with the atom 64 i + j for the
pair i < j, not pysat's numbering), checks every descriptor against its clause, keeps the steps of the
LRAT proof that the empty clause needs, renames the variables to the Lean atoms, and writes one
natural number per derived clause.

Nothing here is trusted by the Lean proof: a wrong descriptor or a wrong step makes the kernel check
fail; it cannot make it succeed.

Step encoding (least significant bits first):
  nl (16 bits) | nl literals, 13 bits each (2 * atom + 1 if positive, 2 * atom if negative) |
  nh (16 bits) | nh hints of 28 bits each.
Hint: bit 0 = 1: an earlier derived clause, bits 1.. its index (0-based, in the kept order);
      bit 0 = 0: an original clause, bits 1.. its descriptor: kind (2 bits) | f1 | f2 | f3 | f4 (6 bits each).
Kinds: 0 transitivity of the triple f1 < f2 < f3, clause number f4 (0, 1, 2 in gw_eq.py's order);
       1 rainbow clause of the 3-term progression with first position f1 and difference f2;
       2 the clause of the 4-term progression with first position f1 and difference f2.

Usage: make_cert.py CNF LRAT OUT.lean
"""
import hashlib, itertools, sys

N, L = 53, 4
CNF_SHA256 = '9008c69718bda8d6999185b7ef4f71c4b64390fa0c5c13b8e13dfd86ab760e40'
LRAT_SHA256 = 'a7a1c1e1a19ce01b11631a101d1c48bb25732a78b1d1f836db1de295b0e82316'


class Pool:
    """pysat.formula.IDPool: ids 1, 2, ... in the order of first use."""
    def __init__(self):
        self.ids, self.objs = {}, {}

    def id(self, obj):
        if obj not in self.ids:
            self.ids[obj] = len(self.ids) + 1
            self.objs[self.ids[obj]] = obj
        return self.ids[obj]


def atom(i, j):
    return 64 * i + j


def desc(kind, *f):
    code = kind
    for t, x in enumerate(f):
        assert 0 <= x < 64
        code |= x << (2 + 6 * t)
    return code


def clauses(pool):
    e = lambda i, j: pool.id(('e', min(i, j), max(i, j)))
    out = []
    for i, j, k in itertools.combinations(range(N), 3):
        out.append(([-e(i, j), -e(j, k), e(i, k)], desc(0, i, j, k, 0)))
        out.append(([-e(i, j), -e(i, k), e(j, k)], desc(0, i, j, k, 1)))
        out.append(([-e(i, k), -e(j, k), e(i, j)], desc(0, i, j, k, 2)))
    for a in range(N):
        for d in range(1, N):
            if a + 2 * d < N:
                p = [a, a + d, a + 2 * d]
                out.append(([e(p[0], p[1]), e(p[1], p[2]), e(p[0], p[2])], desc(1, a, d)))
            if a + (L - 1) * d < N:
                out.append(([-e(a + j * d, a + (j + 1) * d) for j in range(L - 1)], desc(2, a, d)))
    return out


def lean_clause(code):
    """The clause GwH34.descCls computes from a descriptor, as a set of signed Lean atoms (+/-(atom+1))."""
    kind = code & 3
    f = [(code >> (2 + 6 * t)) & 63 for t in range(4)]
    P = lambda i, j: atom(i, j) + 1
    if kind == 0:
        i, j, k, t = f
        assert i < j < k < N and t < 3
        return [{-P(i, j), -P(j, k), P(i, k)}, {-P(i, j), -P(i, k), P(j, k)}, {-P(i, k), -P(j, k), P(i, j)}][t]
    a, d = f[0], f[1]
    if kind == 1:
        assert d >= 1 and a + 2 * d < N
        return {P(a, a + d), P(a + d, a + 2 * d), P(a, a + 2 * d)}
    if kind == 2:
        assert d >= 1 and a + 3 * d < N
        return {-P(a, a + d), -P(a + d, a + 2 * d), -P(a + 2 * d, a + 3 * d)}
    raise ValueError(kind)


def main():
    cnf, proof, out = sys.argv[1], sys.argv[2], sys.argv[3]
    assert hashlib.sha256(open(cnf, 'rb').read()).hexdigest() == CNF_SHA256, 'unexpected CNF file'
    data = open(proof, 'rb').read()
    assert hashlib.sha256(data).hexdigest() == LRAT_SHA256, 'unexpected LRAT file'
    pool = Pool()
    cls = clauses(pool)
    nv = len(pool.ids)
    dimacs = f'p cnf {nv} {len(cls)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c, _ in cls)
    assert hashlib.sha256(dimacs.encode()).hexdigest() == CNF_SHA256, 'CNF differs from gw_eq.py'
    ren = {v: atom(pool.objs[v][1], pool.objs[v][2]) + 1 for v in pool.objs}   # pysat id -> Lean atom + 1
    sgn = lambda x: ren[abs(x)] if x > 0 else -ren[abs(x)]
    for c, code in cls:
        assert {sgn(x) for x in c} == lean_clause(code), (c, code)
    m = len(cls)
    steps, order = {}, []
    for line in data.decode().splitlines():
        t = line.split()
        if len(t) < 2 or t[1] == 'd':
            continue
        cid = int(t[0])
        z = t.index('0', 1)
        steps[cid] = ([int(x) for x in t[1:z]], [int(x) for x in t[z + 1:-1]])
        order.append(cid)
        if z == 1:
            break
    assert not steps[order[-1]][0], 'the proof must end with the empty clause'
    need, stack = {order[-1]}, [order[-1]]
    while stack:
        c = stack.pop()
        for h in steps[c][1]:
            assert h > 0, 'RUP hints only'
            if h > m and h not in need:
                need.add(h)
                stack.append(h)
    kept = [c for c in order if c in need]
    index, codes, nh_orig, nh_der = {}, [], 0, 0
    for cid in kept:
        lits, hints = steps[cid]
        code, pos = 0, 0

        def put(x, w):
            nonlocal code, pos
            assert 0 <= x < (1 << w), (x, w)
            code |= x << pos
            pos += w
        put(len(lits), 16)
        for x in lits:
            a = ren[abs(x)] - 1
            put(2 * a + (1 if x > 0 else 0), 13)
        put(len(hints), 16)
        for h in hints:
            if h <= m:
                nh_orig += 1
                put(cls[h - 1][1] << 1, 28)
            else:
                nh_der += 1
                put((index[h] << 1) | 1, 28)
        index[cid] = len(codes)
        codes.append(code)
    with open(out, 'w') as f:
        f.write('module\n\n@[expose] public section\n\n')
        f.write('/-!\n# The certificate: an LRAT refutation of the any-colour CNF for `(3, 4)` on `[1, 53]`\n\n')
        f.write('Generated by `scripts/make_cert.py` from CaDiCaL 3.0.1\'s LRAT proof (SHA-256\n')
        f.write(f'`{LRAT_SHA256}`) of the CNF\n')
        f.write(f'`cnf/gw_any_53_l4.cnf` of Quantavane\'s `gw_eq.py 53 4 0` (SHA-256\n`{CNF_SHA256}`).\n')
        f.write(f'The {len(codes)} derived clauses that the empty clause needs, of the proof\'s {len(order)}, are kept, in\n')
        f.write(f'order; the last is the empty clause. They have {nh_orig + nh_der:,} hints ({nh_orig:,} to original clauses, named by\n')
        f.write(f'descriptors, and {nh_der:,} to derived clauses). The variables are renamed to the atoms `64 i + j`.\n')
        f.write('The encoding is described in `GwH34.Check` and in the script. This is untrusted data:\n')
        f.write('`GwH34.checkH_sound` holds for every list of natural numbers.\n-/\n\nnamespace GwH34\n\n')
        f.write('/-- The derived clauses of the refutation, one natural number per clause. -/\n')
        f.write('def cert : List Nat := [\n')
        f.write(',\n'.join(hex(s) for s in codes))
        f.write(']\n\nend GwH34\n')
    print(f'{nv} variables, {m} clauses; {len(order)} steps, {len(codes)} kept; hints: {nh_orig} original, {nh_der} derived')


if __name__ == '__main__':
    main()
