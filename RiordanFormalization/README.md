# Lean formalization

This directory contains the Lean 4 formalization of the `F5` results used in
Section 2 of the paper.

The project uses Lean 4.28.0 and mathlib 4.28.0. To check it, run:

```sh
lake exe cache get
lake build
```

The source files are organized as follows:

- `OrderOfPoly.lean`: polynomial order and its divisibility criterion.
- `Periods.lean`: column denominators, period ratios, and the five-adic tower.
- `Blocks.lean`: eventual periodicity and circulant block operations.
- `Riordan.lean`: rational column generating functions and block relations.
- `OrderFormula.lean`: the irreducible-factor formula for polynomial orders.
- `Pascal.lean`: Pascal's array modulo five.
- `Main.lean`: project-wide Lean options.
