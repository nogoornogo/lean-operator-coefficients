#!/usr/bin/env python3
"""Generate an UNTRUSTED rational Lie-basis candidate from ExportMatrices.lean.

No floating-point arithmetic, CAS dependency, or source-text parsing is used.
This is a feasibility experiment, NOT an accepted formal proof. The output
includes bracket provenance, elimination witnesses, and generator-closure
coefficients for a future independent Lean certificate checker.
"""

import argparse
from collections import Counter
from fractions import Fraction
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def add_scaled(target, source, scalar):
    for key, value in source.items():
        new = target.get(key, 0) + scalar * value
        if new:
            target[key] = new
        else:
            target.pop(key, None)


def bracket(left, right):
    result = {}
    right_rows = {}
    left_rows = {}
    for (i, j), value in right.items():
        right_rows.setdefault(i, []).append((j, value))
    for (i, j), value in left.items():
        left_rows.setdefault(i, []).append((j, value))
    for (i, k), value in left.items():
        for j, other in right_rows.get(k, []):
            add_scaled(result, {(i, j): value * other}, 1)
    for (i, k), value in right.items():
        for j, other in left_rows.get(k, []):
            add_scaled(result, {(i, j): value * other}, -1)
    return result


def sparse_matrix(entries):
    result = {}
    for i, j, value in entries:
        check(0 <= i < 27 and 0 <= j < 27, "invalid matrix index")
        check(isinstance(value, int) and value != 0, "nonintegral or zero entry")
        check((i, j) not in result, "duplicate matrix entry")
        result[i, j] = value
    return result


def packed(matrix):
    return [[i, j, str(value)] for (i, j), value in sorted(matrix.items())]


def coefficients(values):
    return [[key, str(value)] for key, value in sorted(values.items())]


class Span:
    def __init__(self):
        self.basis = []
        self.provenance = []
        self.pivots = {}

    def reduce(self, matrix):
        remainder = {key: Fraction(value) for key, value in matrix.items()}
        coords = {}
        for pivot, (row, witness) in sorted(self.pivots.items()):
            factor = remainder.get(pivot, 0)
            if factor:
                add_scaled(remainder, row, -factor)
                add_scaled(coords, witness, factor)
        return remainder, coords

    def insert(self, matrix, provenance):
        remainder, coords = self.reduce(matrix)
        if not remainder:
            return
        check(len(self.basis) < 90, "unexpectedly large candidate; stop bounded experiment")
        pivot = min(remainder)
        factor = remainder[pivot]
        witness = {len(self.basis): Fraction(1)}
        add_scaled(witness, coords, -1)
        self.pivots[pivot] = (
            {key: value / factor for key, value in remainder.items()},
            {key: value / factor for key, value in witness.items()},
        )
        self.basis.append(matrix)
        self.provenance.append(provenance)

    def coordinates(self, matrix):
        remainder, coords = self.reduce(matrix)
        check(not remainder, "candidate span is not closed")
        reconstructed = {}
        for index, value in coords.items():
            add_scaled(reconstructed, self.basis[index], value)
        check(reconstructed == matrix, "coordinate reconstruction failed")
        return coords


def lie_candidate(data, nodes, expected_dimension, expected_roots):
    span = Span()
    generators = []
    labels = []
    for kind in ["raising", "lowering", "diagonal"]:
        for node in nodes:
            matrix = sparse_matrix(data[kind][node])
            span.insert(matrix, {"seed": [kind, node]})
            if kind != "diagonal":
                generators.append(matrix)
                labels.append([kind, node])
    index = 0
    while index < len(span.basis):
        for generator, matrix in enumerate(generators):
            span.insert(bracket(matrix, span.basis[index]),
                        {"bracket": [generator, index]})
        index += 1
    check(len(span.basis) == expected_dimension, "wrong candidate dimension")

    # All data below is verified again exactly, but still outside the Lean kernel.
    closure = []
    for generator, matrix in enumerate(generators):
        for index, basis in enumerate(span.basis):
            coords = span.coordinates(bracket(matrix, basis))
            closure.append([generator, index, coefficients(coords)])
    for pivot, (row, witness) in span.pivots.items():
        reconstructed = {}
        for index, value in witness.items():
            add_scaled(reconstructed, span.basis[index], value)
        check(reconstructed == row and row[pivot] == 1, "bad pivot witness")
        check(min(row) == pivot, "nontriangular pivot")

    weights = data["weights"]
    weight_counts = Counter()
    basis_weights = []
    for matrix in span.basis:
        labels_on_support = {
            tuple(weights[i][k] - weights[j][k] for k in range(6))
            for i, j in matrix
        }
        check(len(labels_on_support) == 1, "basis matrix is not a Cartan eigenvector")
        label = labels_on_support.pop()
        basis_weights.append(label)
        weight_counts[label] += 1
        check(sum(matrix.get((i, i), 0) for i in range(27)) == 0, "nonzero trace")
        if len(nodes) == 5:
            check(all(data["grades"][i] == data["grades"][j] for i, j in matrix),
                  "D5 candidate does not preserve grades")
    zero = (0,) * 6
    check(weight_counts[zero] == len(nodes), "wrong zero-weight dimension")
    nonzero = {weight: count for weight, count in weight_counts.items() if weight != zero}
    check(len(nonzero) == expected_roots and set(nonzero.values()) == {1},
          "wrong root-space count")
    check(all(tuple(-x for x in weight) in nonzero for weight in nonzero),
          "root candidates are not paired")
    for matrix in span.basis:
        span.coordinates({(j, i): value for (i, j), value in matrix.items()})

    return {
        "summary": {
            "dimension_candidate": len(span.basis),
            "zero_weight_dimension": weight_counts[zero],
            "nonzero_weight_spaces": len(nonzero),
            "basis_nonzero_entries": sum(map(len, span.basis)),
            "generator_closure_equations": len(closure),
            "closure_coefficient_count": sum(len(row[2]) for row in closure),
            "transpose_stable": True,
        },
        "generators": labels,
        "basis": [
            {"entries": packed(matrix), "provenance": origin, "weight": weight}
            for matrix, origin, weight in zip(span.basis, span.provenance, basis_weights)
        ],
        "pivots": [
            {"position": pivot, "row": packed(row), "basis_coefficients": coefficients(witness)}
            for pivot, (row, witness) in sorted(span.pivots.items())
        ],
        "generator_closure": closure,
    }


def validate_input(data):
    check(data["schema"] == 1, "unknown input schema")
    check(len(data["weights"]) == 27 and all(len(w) == 6 for w in data["weights"]),
          "wrong weight shape")
    check(data["d5_nodes"] == [5, 4, 3, 1, 2], "unexpected D5 convention")
    check(Counter(data["grades"]) == {1: 16, -2: 10, 4: 1}, "wrong grading counts")
    for node in range(6):
        e = sparse_matrix(data["raising"][node])
        f = sparse_matrix(data["lowering"][node])
        h = sparse_matrix(data["diagonal"][node])
        check({(j, i): x for (i, j), x in e.items()} == f, "adjoint mismatch")
        check(h == {(i, i): w[node] for i, w in enumerate(data["weights"]) if w[node]},
              "diagonal-weight mismatch")
        check(bracket(e, f) == h, "sl2 bracket mismatch")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="JSON emitted by ExportMatrices.lean")
    parser.add_argument("--summary", action="store_true", help="omit the candidate witnesses")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as handle:
        data = json.load(handle)
    validate_input(data)
    result = {
        "status": "EXTERNAL CANDIDATE ONLY: not a Lean proof",
        "E6": lie_candidate(data, list(range(6)), 78, 72),
        "D5": lie_candidate(data, data["d5_nodes"], 45, 40),
    }
    if args.summary:
        result = {key: value["summary"] if key != "status" else value
                  for key, value in result.items()}
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
