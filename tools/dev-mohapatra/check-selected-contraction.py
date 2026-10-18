"""Finite diagnostic of the fixed source monomial; Lean proves its evaluation independently."""
from itertools import permutations

LABELS = (0, 0, 0, 1, 0, 1)


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))


def eps3(a, b, c):
    return sign((a, b, c)) if len({a, b, c}) == 3 else 0


def value(colors, spins, p):
    c, s = lambda i: colors[p[i]], lambda i: spins[p[i]]
    return eps3(c(0), c(1), c(3)) * eps3(c(2), c(4), c(5)) * (s(2)-s(0)) * (s(3)-s(1)) * (s(5)-s(4))


def descend(colors, spins):
    total = 0
    count = 0
    for up in ((0, 2), (2, 0)):
        for down in permutations((1, 3, 4, 5)):
            p = (up[0], down[0], up[1], down[1], down[2], down[3])
            count += 1
            if all(LABELS[p[i]] == LABELS[i] for i in range(6)):
                total += sign(p) * value(colors, spins, p)
    assert count == 48
    return total


if __name__ == "__main__":
    original_colors, original_spins = (0, 1, 0, 2, 1, 2), (0, 0, 1, 1, 0, 1)
    assert value(original_colors, original_spins, tuple(range(6))) == 1
    assert descend(original_colors, original_spins) == 0
    assert descend((0, 2, 2, 1, 0, 1), (0, 0, 1, 0, 1, 1)) == -2
    print("48 within-species permutations: cancellation and selected nonzero controls passed")
