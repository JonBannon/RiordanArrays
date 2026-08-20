import Mathlib

/-!
# The order of a polynomial over `F₅`

For a polynomial `Q` over `F₅ = ZMod 5` with `Q(0) ≠ 0`, the *order* `ord Q` is the least
`N ≥ 1` such that `Q ∣ tᴺ - 1`.  It is the least eventual period of every linear recurring
sequence whose generating function has denominator `Q`.

We define `polyOrd Q` as the multiplicative order of the image of `t` in `F₅[t]/(Q)`; this makes
the fundamental divisibility criterion `polyOrd Q ∣ N ↔ Q ∣ tᴺ - 1` hold unconditionally.
-/

open Polynomial

namespace RiordanF5

/-- The field with five elements. -/
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The order of a polynomial `Q` over `F₅`: the least `N ≥ 1` with `Q ∣ tᴺ - 1`
(equal to `0` if no such `N` exists, i.e. when `Q(0) = 0` or `Q = 0`).
It is defined as the multiplicative order of the residue of `t` in `F₅[t]/(Q)`. -/
noncomputable def polyOrd (Q : F5[X]) : ℕ := orderOf (AdjoinRoot.root Q)

/-- Fundamental divisibility criterion: `Q ∣ tᴺ - 1` exactly when the order of `Q` divides `N`. -/
theorem polyOrd_dvd_iff (Q : F5[X]) (N : ℕ) : polyOrd Q ∣ N ↔ Q ∣ (X : F5[X]) ^ N - 1 := by
  rw [polyOrd, orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    have : (AdjoinRoot.mk Q) ((X : F5[X]) ^ N - 1) = 0 := by
      rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, h, sub_self]
    exact AdjoinRoot.mk_eq_zero.mp this
  · intro h
    have : (AdjoinRoot.mk Q) ((X : F5[X]) ^ N - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr h
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at this
    exact this

theorem polyOrd_dvd_self (Q : F5[X]) : Q ∣ (X : F5[X]) ^ (polyOrd Q) - 1 :=
  (polyOrd_dvd_iff Q _).mp dvd_rfl

theorem polyOrd_le {Q : F5[X]} {N : ℕ} (hN : 0 < N) (h : Q ∣ (X : F5[X]) ^ N - 1) :
    polyOrd Q ≤ N :=
  Nat.le_of_dvd hN ((polyOrd_dvd_iff Q N).mpr h)

/-- If `Q ≠ 0` and `Q(0) ≠ 0` then `Q` has a positive order. -/
theorem polyOrd_pos {Q : F5[X]} (hQ : Q ≠ 0) (h0 : Q.coeff 0 ≠ 0) : 0 < polyOrd Q := by
  haveI : Finite (AdjoinRoot Q) := by
    have pb := AdjoinRoot.powerBasis (K := F5) hQ
    have : Module.Finite F5 (AdjoinRoot Q) := pb.finite
    exact Module.finite_of_finite F5
  -- `t` is a unit modulo `Q`
  have hcop : IsCoprime (X : F5[X]) Q :=
    (Polynomial.irreducible_X (R := F5)).coprime_iff_not_dvd.mpr
      (fun h => h0 (Polynomial.X_dvd_iff.mp h))
  obtain ⟨a, b, hab⟩ := hcop
  have hunit : IsUnit (AdjoinRoot.root Q) := by
    refine IsUnit.of_mul_eq_one (b := AdjoinRoot.mk Q a) ?_
    have := congrArg (AdjoinRoot.mk Q) hab
    simp only [map_add, map_mul, map_one, AdjoinRoot.mk_X,
      AdjoinRoot.mk_self, mul_zero, add_zero] at this
    rw [mul_comm]
    exact this
  obtain ⟨u, hu⟩ := hunit
  rw [polyOrd, ← hu, orderOf_units]
  exact orderOf_pos u

end RiordanF5
