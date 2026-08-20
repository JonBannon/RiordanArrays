import RequestProject.OrderOfPoly

/-!
# Periods of the columns of a rational Riordan array over `F₅`

Let `R = (g, f) = (p₁/p₂, p₃/p₄)` be a Riordan array over `F₅ = ZMod 5`.
The generating function of its `k`-th column is

  `H k = g * f ^ k = (p₁ p₃ ^ k) / (p₂ p₄ ^ k)`,

so (in the absence of cancellation) the denominator of column `k` is `Q k = p₂ * p₄ ^ k`
and the least eventual period of column `k` is `π k = polyOrd (Q k)`.

The main results here are purely about these orders:

* `blockPeriod_dvd_succ`  : `π k ∣ π (k+1)`;
* `blockPeriod_succ_dvd`  : `π (k+1) ∣ 5 * π k` for `k ≥ 1`;
* `blockPeriod_ratio`     : for `k ≥ 1`, `π (k+1) = π k` or `π (k+1) = 5 * π k`;
* `blockPeriod_tower`     : hence `π k = π 1 * 5 ^ (t k)` for a monotone `t` — the periods
  form plateaux inside a `5`-adic tower, jumping by factors of `5`.
-/

open Polynomial

namespace RiordanF5

/-- Freshman's dream in characteristic `5`: `t^{5N} - 1 = (t^N - 1)^5`. -/
theorem X_pow_sub_one_pow_five (N : ℕ) :
    ((X : F5[X]) ^ N - 1) ^ 5 = (X : F5[X]) ^ (5 * N) - 1 := by
  have h : ((X : F5[X]) ^ N - 1) ^ 5 = ((X : F5[X]) ^ N) ^ 5 - 1 ^ 5 :=
    sub_pow_char (R := F5[X]) _ _
  rw [h, one_pow, ← pow_mul, mul_comm N 5]

/-- The denominator of the `k`-th column of the Riordan array `(p₁/p₂, p₃/p₄)`. -/
noncomputable def colDen (p2 p4 : F5[X]) (k : ℕ) : F5[X] := p2 * p4 ^ k

/-- The eventual period `π k` of the `k`-th column of the Riordan array `(p₁/p₂, p₃/p₄)`:
the order of its denominator `p₂ p₄ᵏ`.  It is the *least* eventual period whenever the
fraction is in lowest terms; see `colGF_least_period`. -/
noncomputable def blockPeriod (p2 p4 : F5[X]) (k : ℕ) : ℕ := polyOrd (colDen p2 p4 k)

variable {p2 p4 : F5[X]}

theorem colDen_dvd_succ (k : ℕ) : colDen p2 p4 k ∣ colDen p2 p4 (k + 1) := by
  simp only [colDen, pow_succ]
  exact ⟨p4, by ring⟩

/-- Periods can only grow: `π k ∣ π (k+1)`. -/
theorem blockPeriod_dvd_succ (k : ℕ) :
    blockPeriod p2 p4 k ∣ blockPeriod p2 p4 (k + 1) := by
  rw [blockPeriod, polyOrd_dvd_iff]
  exact (colDen_dvd_succ k).trans (polyOrd_dvd_self _)

/-- For `k ≥ 1`, the period of column `k+1` divides five times the period of column `k`. -/
theorem blockPeriod_succ_dvd {k : ℕ} (hk : 1 ≤ k) :
    blockPeriod p2 p4 (k + 1) ∣ 5 * blockPeriod p2 p4 k := by
  rw [blockPeriod, polyOrd_dvd_iff, ← X_pow_sub_one_pow_five]
  set D : F5[X] := (X : F5[X]) ^ blockPeriod p2 p4 k - 1 with hD
  have hQ : colDen p2 p4 k ∣ D := polyOrd_dvd_self _
  -- `p₂ p₄^{k+1} ∣ (p₂ p₄^k)^2 ∣ D^2 ∣ D^5`
  have h1 : colDen p2 p4 (k + 1) ∣ (colDen p2 p4 k) ^ 2 := by
    simp only [colDen]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨p2 * p4 ^ j, ?_⟩
    subst hj
    ring
  have h2 : (colDen p2 p4 k) ^ 2 ∣ D ^ 2 := pow_dvd_pow_of_dvd hQ 2
  have h3 : D ^ 2 ∣ D ^ 5 := pow_dvd_pow D (by norm_num)
  exact h1.trans (h2.trans h3)

/-- **The period ratio is `1` or `5`.** For `k ≥ 1` the eventual periods of consecutive
columns satisfy `π (k+1) / π k ∈ {1, 5}`. -/
theorem blockPeriod_ratio {k : ℕ} (hk : 1 ≤ k) (hpos : 0 < blockPeriod p2 p4 k) :
    blockPeriod p2 p4 (k + 1) = blockPeriod p2 p4 k ∨
      blockPeriod p2 p4 (k + 1) = 5 * blockPeriod p2 p4 k := by
  obtain ⟨d, hd⟩ := blockPeriod_dvd_succ (p2 := p2) (p4 := p4) k
  have hdvd : blockPeriod p2 p4 k * d ∣ blockPeriod p2 p4 k * 5 := by
    rw [← hd, mul_comm (blockPeriod p2 p4 k) 5]
    exact blockPeriod_succ_dvd hk
  have hd5 : d ∣ 5 := (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) d hd5) with h | h
  · left; rw [hd, h, mul_one]
  · right; rw [hd, h, mul_comm]

/-- The positivity hypothesis holds as soon as the denominators are nonzero at `0`. -/
theorem blockPeriod_pos (h2 : p2 ≠ 0) (h4 : p4 ≠ 0) (h2c : p2.coeff 0 ≠ 0)
    (h4c : p4.coeff 0 ≠ 0) (k : ℕ) : 0 < blockPeriod p2 p4 k := by
  refine polyOrd_pos ?_ ?_
  · exact mul_ne_zero h2 (pow_ne_zero _ h4)
  · rw [colDen, Polynomial.mul_coeff_zero,
      show (p4 ^ k).coeff 0 = (p4.coeff 0) ^ k by
        simpa using map_pow (Polynomial.constantCoeff (R := F5)) p4 k]
    exact mul_ne_zero h2c (pow_ne_zero _ h4c)

/-- **The `5`-adic tower of periods.** From column `1` on, every period is `π 1` times a
power of `5`, and the exponent is nondecreasing: the periods sit in plateaux and jump by a
factor `5` at certain columns. -/
theorem blockPeriod_tower (h2 : p2 ≠ 0) (h4 : p4 ≠ 0) (h2c : p2.coeff 0 ≠ 0)
    (h4c : p4.coeff 0 ≠ 0) :
    ∃ t : ℕ → ℕ, Monotone t ∧ t 1 = 0 ∧
      ∀ k, 1 ≤ k → blockPeriod p2 p4 k = blockPeriod p2 p4 1 * 5 ^ t k := by
  classical
  -- build the exponent sequence recursively
  refine ⟨fun k => Nat.rec 0 (fun j tj =>
      if 1 ≤ j ∧ blockPeriod p2 p4 (j + 1) = 5 * blockPeriod p2 p4 j then tj + 1 else tj) k,
    ?_, rfl, ?_⟩
  · refine monotone_nat_of_le_succ (fun n => ?_)
    dsimp only
    split <;> omega
  · intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hk with h1 | h1
      · -- n + 1 = 1
        have hn : n = 0 := by omega
        subst hn
        simp
      · have hn : 1 ≤ n := by omega
        have hpos := blockPeriod_pos h2 h4 h2c h4c (p2 := p2) (p4 := p4) n
        have hstep := blockPeriod_ratio (p2 := p2) (p4 := p4) hn hpos
        dsimp only
        rcases hstep with h | h
        · rw [if_neg (by rintro ⟨-, h5⟩; omega), h, ih hn]
        · rw [if_pos ⟨hn, h⟩, h, ih hn]
          ring

end RiordanF5
