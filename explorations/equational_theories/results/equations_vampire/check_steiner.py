"""Check the two Steiner identifications of Section 4 of docs/exploration.tex ("Where the experts
differ") for the magmas of this result, from the definitions, and by an explicit isomorphism to the
textbook constructions (so not relying on the uniqueness of the Steiner triple systems on 7 and 9
points). Associativity and mediality are checked directly too.

M21 (size 10): a Steiner loop: a commutative loop with x(xy) = y; its triples {x, y, xy}, x != y,
x, y != e, form a Steiner triple system on 9 points; isomorphic to the Steiner loop of AG(2, 3).
M34 (size 7): a Steiner quasigroup: idempotent, commutative, x(xy) = y; its triples form an STS(7);
isomorphic to the quasigroup of the Fano plane, x * y = the third point on the line through x, y.

usage: python check_steiner.py [MAGMAS_JSON]   (default: magmas.json next to this script)
"""
import itertools
import json
import sys
from pathlib import Path

path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / "magmas.json"
ms = {m["name"]: m["table"] for m in json.loads(path.read_text())}


def is_latin(t):
    n = len(t)
    return all(sorted(r) == list(range(n)) for r in t) and all(sorted(t[x][y] for x in range(n)) == list(range(n)) for y in range(n))


def commutative(t):
    return all(t[x][y] == t[y][x] for x in range(len(t)) for y in range(len(t)))


def steiner_identity(t):  # x(xy) = y
    return all(t[x][t[x][y]] == y for x in range(len(t)) for y in range(len(t)))


def associative(t):
    r = range(len(t))
    return all(t[t[x][y]][z] == t[x][t[y][z]] for x in r for y in r for z in r)


def medial(t):
    r = range(len(t))
    return all(t[t[x][y]][t[z][w]] == t[t[x][z]][t[y][w]] for x in r for y in r for z in r for w in r)


def triples(t, points):
    return {frozenset((x, y, t[x][y])) for x in points for y in points if x != y}


def is_sts(blocks, points):
    pairs = {}
    for b in blocks:
        if len(b) != 3 or not b <= set(points):
            return False
        for p in itertools.combinations(sorted(b), 2):
            pairs[p] = pairs.get(p, 0) + 1
    return set(pairs) == set(itertools.combinations(sorted(points), 2)) and set(pairs.values()) == {1}


def isomorphism(t, u, fixed=()):
    """A bijection f with f(t[x][y]) = u[f(x)][f(y)], extending the pairs in fixed, or None."""
    n = len(t)
    free_src = [x for x in range(n) if x not in dict(fixed)]
    free_dst = [y for y in range(n) if y not in dict(fixed).values()]
    for perm in itertools.permutations(free_dst):
        f = dict(fixed) | dict(zip(free_src, perm))
        if all(f[t[x][y]] == u[f[x]][f[y]] for x in range(n) for y in range(n)):
            return f
    return None


# M21: Steiner loop of order 10.
t = ms["M21"]
n = len(t)
e = [x for x in range(n) if all(t[x][y] == y and t[y][x] == y for y in range(n))]
print("M21: size", n, "| latin (loop)", is_latin(t), "| identity", e, "| commutative", commutative(t),
      "| x(xy)=y", steiner_identity(t), "| xx=e", all(t[x][x] == e[0] for x in range(n)),
      "| associative", associative(t), "| medial", medial(t))
pts = [x for x in range(n) if x != e[0]]
blocks = triples(t, pts)
print("  triples {x, y, xy}:", len(blocks), "| STS(9):", is_sts(blocks, pts))
# The Steiner loop of AG(2, 3): points Z3^2 (0..8), e = 9; three distinct points are collinear iff
# they sum to 0, so the third point on the line through p, q is -(p + q).
P = [(a, b) for a in range(3) for b in range(3)]
ag = [[None] * 10 for _ in range(10)]
for i in range(10):
    ag[i][9] = ag[9][i] = i
for i, p in enumerate(P):
    for j, q in enumerate(P):
        ag[i][j] = 9 if i == j else P.index(((-p[0] - q[0]) % 3, (-p[1] - q[1]) % 3))
assert is_sts(triples(ag, range(9)), range(9))
f = isomorphism(t, ag, fixed=[(e[0], 9)])
print("  isomorphic to the Steiner loop of AG(2,3):", f is not None, f)

# M34: Steiner quasigroup of order 7.
t = ms["M34"]
n = len(t)
print("M34: size", n, "| latin (quasigroup)", is_latin(t), "| idempotent", all(t[x][x] == x for x in range(n)),
      "| commutative", commutative(t), "| x(xy)=y", steiner_identity(t), "| associative", associative(t),
      "| medial", medial(t))
blocks = triples(t, range(n))
print("  triples:", len(blocks), "| STS(7):", is_sts(blocks, range(n)))
# The Fano plane: points the nonzero vectors of F2^3 (1..7, as 0..6); the line through p, q is
# {p, q, p xor q}.
fano = [[x if x == y else ((x + 1) ^ (y + 1)) - 1 for y in range(7)] for x in range(7)]
assert is_sts(triples(fano, range(7)), range(7))
f = isomorphism(t, fano)
print("  isomorphic to the quasigroup of the Fano plane:", f is not None, f)
