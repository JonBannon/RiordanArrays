import RequestProject.Riordan

/-!
# The Pascal example

For `g = 1/(1-t)` and `f = t/(1-t)` (Pascal's triangle mod 5) we have `p₁ = 1`, `p₂ = 1 - t`,
`p₃ = t`, `p₄ = 1 - t`, so the denominator of column `k` is `(1-t)^{k+1}` and

  `π k = 5 ^ ⌈log₅ (k+1)⌉`.

Thus the periods are `1, 5, 5, 5, 5, 25, …, 25, 125, …`, and the relation between
neighbouring blocks is `(1-t) B_{k+1} ≡ t B_k`, i.e. discrete antidifferentiation.
-/

open Polynomial

namespace RiordanF5

/-- In characteristic `5`, `(t - 1)^{5^j} = t^{5^j} - 1`. -/
theorem X_sub_one_pow_five_pow (j : ℕ) :
    ((X : F5[X]) - 1) ^ (5 ^ j) = (X : F5[X]) ^ (5 ^ j) - 1 := by
  induction j with
  | zero => simp
  | succ i ih =>
    have h : (5 : ℕ) ^ (i + 1) = 5 * 5 ^ i := by ring
    rw [h, pow_mul', ih, X_pow_sub_one_pow_five]

theorem natDegree_one_sub_X_pow (m : ℕ) : ((1 - X : F5[X]) ^ m).natDegree = m := by
  rw [Polynomial.natDegree_pow]
  have : ((1 - X : F5[X])).natDegree = 1 := by compute_degree!
  rw [this, mul_one]

/-- The order of `(1 - t)^m` over `F₅` is `5 ^ ⌈log₅ m⌉`. -/
theorem polyOrd_one_sub_X_pow (m : ℕ) :
    polyOrd ((1 - X : F5[X]) ^ m) = 5 ^ Nat.clog 5 m := by
  set j := Nat.clog 5 m with hj
  have hle : m ≤ 5 ^ j := Nat.le_pow_clog (by norm_num) m
  -- the order divides `5 ^ j`
  have hdvd : polyOrd ((1 - X : F5[X]) ^ m) ∣ 5 ^ j := by
    rw [polyOrd_dvd_iff, ← X_sub_one_pow_five_pow j]
    exact dvd_trans ⟨(-1) ^ m, by rw [← mul_pow]; ring_nf⟩ (pow_dvd_pow _ hle)
  -- hence it is `5 ^ i` for some `i ≤ j`
  obtain ⟨i, hi, hpow⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hdvd
  -- and `m ≤ 5 ^ i` by comparing degrees
  have hdvd2 : (1 - X : F5[X]) ^ m ∣ ((X : F5[X]) - 1) ^ (5 ^ i) := by
    rw [X_sub_one_pow_five_pow i, ← hpow]
    exact polyOrd_dvd_self _
  have hne : ((X : F5[X]) - 1) ^ (5 ^ i) ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    have := congrArg (fun p => Polynomial.coeff p 1) h
    simp [Polynomial.coeff_one] at this
  have hdegXi : ((X : F5[X]) ^ (5 ^ i) - 1).natDegree = 5 ^ i := by compute_degree!
  have hdeg : m ≤ 5 ^ i := by
    have hle2 := Polynomial.natDegree_le_of_dvd hdvd2 hne
    rwa [natDegree_one_sub_X_pow, X_sub_one_pow_five_pow i, hdegXi] at hle2
  have : j ≤ i := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hdeg
  rw [hpow]
  congr 1
  omega

/-- **Periods of Pascal's array mod 5.**  The `k`-th column of the Riordan array
`(1/(1-t), t/(1-t))` has least eventual period `5 ^ ⌈log₅ (k+1)⌉`. -/
theorem pascal_blockPeriod (k : ℕ) :
    blockPeriod (1 - X) (1 - X) k = 5 ^ Nat.clog 5 (k + 1) := by
  rw [blockPeriod, colDen, ← pow_succ', polyOrd_one_sub_X_pow]

example : blockPeriod (1 - X) (1 - X) 0 = 1 := by
  rw [pascal_blockPeriod]; norm_num

example : blockPeriod (1 - X) (1 - X) 4 = 5 := by
  rw [pascal_blockPeriod]; norm_num [Nat.clog]

example : blockPeriod (1 - X) (1 - X) 5 = 25 := by
  rw [pascal_blockPeriod]; norm_num [Nat.clog]

example : blockPeriod (1 - X) (1 - X) 24 = 25 := by
  rw [pascal_blockPeriod]; norm_num [Nat.clog]

example : blockPeriod (1 - X) (1 - X) 25 = 125 := by
  rw [pascal_blockPeriod]; norm_num [Nat.clog]

/-- **Pascal's array: the block relation is discrete antidifferentiation.**
With `N = π (k+1)`, the blocks satisfy `(1 - t) B_{k+1} = t B_k` in `F₅[t]/(tᴺ-1)`. -/
theorem pascal_block_relation (k : ℕ) :
    ∃ n0 : ℕ, ∀ M, n0 ≤ M →
      AdjoinRoot.mk _ (1 - X : F5[X])
          * block (blockPeriod (1 - X) (1 - X) (k + 1)) (colGF 1 (1 - X) X (1 - X) (k + 1)) M
        = AdjoinRoot.mk _ (X : F5[X])
          * block (blockPeriod (1 - X) (1 - X) (k + 1)) (colGF 1 (1 - X) X (1 - X) k) M := by
  refine riordan_block_relation ?_ ?_ k <;> simp

/-- For Pascal's array the circulant `p₄(S_N) = (1 - S_N)` is singular, so the block relation
`(1 - S_N) C_{k+1} = S_N C_k` really is only an equation: the antiderivative is not unique. -/
theorem pascal_p4_singular (k : ℕ) :
    ¬ IsUnit (AdjoinRoot.mk ((X : F5[X]) ^ (blockPeriod (1 - X) (1 - X) (k + 1)) - 1)
      (1 - X : F5[X])) := by
  set N := blockPeriod (1 - X : F5[X]) (1 - X) (k + 1) with hNdef
  have hN : 0 < N := by
    rw [hNdef, pascal_blockPeriod]
    positivity
  have hdvd : (1 - X : F5[X]) ∣ (X : F5[X]) ^ N - 1 :=
    dvd_trans (dvd_mul_right _ _) (polyOrd_dvd_self (colDen (1 - X : F5[X]) (1 - X) (k + 1)))
  have hdeg : 0 < ((1 : F5[X]) - X).natDegree := by
    have : ((1 - X : F5[X])).natDegree = 1 := by compute_degree!
    omega
  exact mk_not_isUnit_of_dvd hN hdvd hdeg

end RiordanF5
