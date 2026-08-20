#!/usr/bin/env python3
"""Test a two-state Yang-Baxter operator from an ordinary Riordan array.

Let R be the 4 by 4 principal truncation of (g,f), normalized by g(0)=1.
We regard R as an operator on V tensor V for dim(V)=2 and compute the
braided Yang-Baxter defect

    (R tensor I)(I tensor R)(R tensor I)
      - (I tensor R)(R tensor I)(I tensor R).

The selected entries printed below form a short certificate that an
invertible Riordan truncation satisfying the equation must be the identity.

Install the experimental dependency with
``python3 -m pip install -r requirements-experiments.txt``.
"""

import sympy as sp


def riordan_truncation():
    """Return the symbolic 4 by 4 truncation and its six parameters."""
    g1, g2, g3, f1, f2, f3 = sp.symbols("g1 g2 g3 f1 f2 f3")
    matrix = sp.Matrix(
        [
            [1, 0, 0, 0],
            [g1, f1, 0, 0],
            [g2, f2 + g1 * f1, f1**2, 0],
            [
                g3,
                f3 + g1 * f2 + g2 * f1,
                2 * f1 * f2 + g1 * f1**2,
                f1**3,
            ],
        ]
    )
    return matrix, (g1, g2, g3, f1, f2, f3)


def main():
    matrix, parameters = riordan_truncation()
    g1, g2, g3, f1, f2, f3 = parameters
    identity = sp.eye(2)
    r12 = sp.kronecker_product(matrix, identity)
    r23 = sp.kronecker_product(identity, matrix)
    defect = r12 * r23 * r12 - r23 * r12 * r23

    stages = [
        ("initial", {}, [(1, 0), (1, 1)]),
        ("after g1=0 and f1=1", {g1: 0, f1: 1}, [(2, 1), (2, 0)]),
        (
            "after f2=0 and g2=0",
            {g1: 0, f1: 1, f2: 0, g2: 0},
            [(3, 0), (3, 1)],
        ),
    ]

    print("R =")
    sp.print_latex(matrix)
    print("\nSelected entries of the Yang-Baxter defect:")
    for label, substitutions, entries in stages:
        print(f"\n{label}")
        for row, column in entries:
            value = sp.factor(defect[row, column].subs(substitutions))
            print(f"  D[{row},{column}] = {value}")

    final = matrix.subs({g1: 0, f1: 1, f2: 0, g2: 0, g3: 0, f3: 0})
    assert final == sp.eye(4)
    assert defect.subs({g1: 0, f1: 1, f2: 0, g2: 0, g3: 0, f3: 0}).is_zero_matrix
    print("\nConclusion: invertibility gives f1 != 0, and the selected entries")
    print("force R = I_4. A general nonzero g(0) only gives a scalar multiple.")


if __name__ == "__main__":
    main()
