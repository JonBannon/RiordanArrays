import RequestProject.Blocks

/-!
# Rational Riordan arrays over `F₅` and their periodic blocks

The Riordan array `R = (g, f) = (p₁/p₂, p₃/p₄)` over `F₅` has `k`-th column generating
function

  `H k = g · f ^ k = (p₁ p₃ᵏ) / (p₂ p₄ᵏ)`.

Its denominator is `colDen p₂ p₄ k = p₂ p₄ᵏ`, so its least eventual period divides
`π k = blockPeriod p₂ p₄ k`.

Main results:

* `colGF_rel`                : `p₄ · H (k+1) = p₃ · H k`;
* `colGF_eventuallyPeriodic` : the coefficients of column `k` are eventually `N`-periodic
  whenever `π k ∣ N`;
* `riordan_block_relation`   : with `N = π (k+1)`, the periodic blocks of columns `k` and
  `k+1` satisfy the singular circulant equation `p₄(S_N) C_{k+1} = p₃(S_N) C_k`;
* `riordan_block_iota`       : the length-`π (k+1)` block of column `k` is its length-`π k`
  block repeated `π (k+1) / π k` times, i.e. it is `ι C_k`.
-/

open Polynomial

namespace RiordanF5

variable {p1 p2 p3 p4 : F5[X]}

/-- The generating function of the `k`-th column of the Riordan array `(p₁/p₂, p₃/p₄)`,
namely `g f ᵏ = (p₁ p₃ᵏ)/(p₂ p₄ᵏ)`. -/
noncomputable def colGF (p1 p2 p3 p4 : F5[X]) (k : ℕ) : PowerSeries F5 :=
  ((p1 * p3 ^ k : F5[X]) : PowerSeries F5) * (((p2 * p4 ^ k : F5[X]) : PowerSeries F5))⁻¹

theorem colDen_coeff_zero (h2c : p2.coeff 0 ≠ 0) (h4c : p4.coeff 0 ≠ 0) (k : ℕ) :
    (colDen p2 p4 k).coeff 0 ≠ 0 := by
  rw [colDen, Polynomial.mul_coeff_zero,
    show (p4 ^ k).coeff 0 = (p4.coeff 0) ^ k by
      simpa using map_pow (Polynomial.constantCoeff (R := F5)) p4 k]
  exact mul_ne_zero h2c (pow_ne_zero _ h4c)

/-- The column generating function has denominator `p₂ p₄ᵏ`. -/
theorem colGF_spec (h2c : p2.coeff 0 ≠ 0) (h4c : p4.coeff 0 ≠ 0) (k : ℕ) :
    ((colDen p2 p4 k : F5[X]) : PowerSeries F5) * colGF p1 p2 p3 p4 k
      = ((p1 * p3 ^ k : F5[X]) : PowerSeries F5) := by
  have hc : PowerSeries.constantCoeff ((colDen p2 p4 k : F5[X]) : PowerSeries F5) ≠ 0 := by
    simpa using colDen_coeff_zero h2c h4c k
  rw [colGF, colDen]
  rw [show ((p2 * p4 ^ k : F5[X]) : PowerSeries F5) = ((colDen p2 p4 k : F5[X]) : PowerSeries F5)
      from rfl]
  rw [← mul_assoc, mul_comm ((colDen p2 p4 k : F5[X]) : PowerSeries F5), mul_assoc,
    PowerSeries.mul_inv_cancel _ hc, mul_one]

/-- **The defining relation between neighbouring columns**: `p₄ H_{k+1} = p₃ H_k`. -/
theorem colGF_rel (h4c : p4.coeff 0 ≠ 0) (k : ℕ) :
    ((p4 : F5[X]) : PowerSeries F5) * colGF p1 p2 p3 p4 (k + 1)
      = ((p3 : F5[X]) : PowerSeries F5) * colGF p1 p2 p3 p4 k := by
  have hc4 : PowerSeries.constantCoeff ((p4 : F5[X]) : PowerSeries F5) ≠ 0 := by simpa using h4c
  have hsplit : ((p2 * p4 ^ (k + 1) : F5[X]) : PowerSeries F5)
      = ((p2 * p4 ^ k : F5[X]) : PowerSeries F5) * ((p4 : F5[X]) : PowerSeries F5) := by
    push_cast; ring
  simp only [colGF, hsplit, PowerSeries.mul_inv_rev]
  have hnum : ((p1 * p3 ^ (k + 1) : F5[X]) : PowerSeries F5)
      = ((p3 : F5[X]) : PowerSeries F5) * ((p1 * p3 ^ k : F5[X]) : PowerSeries F5) := by
    push_cast; ring
  rw [hnum]
  have h4 : ((p4 : F5[X]) : PowerSeries F5) * (((p4 : F5[X]) : PowerSeries F5))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hc4
  calc ((p4 : F5[X]) : PowerSeries F5)
        * ((p3 : F5[X]) * ((p1 * p3 ^ k : F5[X]) : PowerSeries F5)
          * ((((p4 : F5[X]) : PowerSeries F5))⁻¹ * ((((p2 * p4 ^ k : F5[X]))
              : PowerSeries F5))⁻¹))
      = (((p4 : F5[X]) : PowerSeries F5) * (((p4 : F5[X]) : PowerSeries F5))⁻¹)
          * (((p3 : F5[X]) : PowerSeries F5) * (((p1 * p3 ^ k : F5[X]) : PowerSeries F5)
            * ((((p2 * p4 ^ k : F5[X])) : PowerSeries F5))⁻¹)) := by ring
    _ = ((p3 : F5[X]) : PowerSeries F5) * (((p1 * p3 ^ k : F5[X]) : PowerSeries F5)
            * ((((p2 * p4 ^ k : F5[X])) : PowerSeries F5))⁻¹) := by rw [h4, one_mul]

theorem EventuallyPeriodic.mono {H : PowerSeries F5} {N n0 n1 : ℕ}
    (h : EventuallyPeriodic H N n0) (hn : n0 ≤ n1) : EventuallyPeriodic H N n1 :=
  fun n hn' => h n (le_trans hn hn')

/-- The coefficients of column `k` are eventually `N`-periodic whenever `π k ∣ N`. -/
theorem colGF_eventuallyPeriodic (h2c : p2.coeff 0 ≠ 0) (h4c : p4.coeff 0 ≠ 0) (k : ℕ)
    {N : ℕ} (hdvd : blockPeriod p2 p4 k ∣ N) :
    ∃ n0, EventuallyPeriodic (colGF p1 p2 p3 p4 k) N n0 :=
  eventuallyPeriodic_of_den (colGF_spec h2c h4c k)
    ((polyOrd_dvd_iff _ _).mp hdvd)

/-- **The circulant relation between the periodic blocks of consecutive columns.**
With `N = π (k+1)` (so that both columns are `N`-periodic), the blocks of columns `k` and
`k+1`, read from any sufficiently late position `M`, satisfy

  `p₄(S_N) · C_{k+1} = p₃(S_N) · C_k`   in   `F₅[t]/(tᴺ - 1)`.

Note that `p₄(S_N)` is *singular* whenever `p₄ ∣ tᴺ - 1`, so this is an equation, not a map. -/
theorem riordan_block_relation (h2c : p2.coeff 0 ≠ 0) (h4c : p4.coeff 0 ≠ 0) (k : ℕ) :
    ∃ n0 : ℕ, ∀ M, n0 ≤ M →
      AdjoinRoot.mk _ p4 * block (blockPeriod p2 p4 (k + 1)) (colGF p1 p2 p3 p4 (k + 1)) M
        = AdjoinRoot.mk _ p3 * block (blockPeriod p2 p4 (k + 1)) (colGF p1 p2 p3 p4 k) M := by
  set N := blockPeriod p2 p4 (k + 1) with hN
  obtain ⟨nA, hA⟩ := colGF_eventuallyPeriodic (p1 := p1) (p3 := p3) h2c h4c k
    (dvd_trans (blockPeriod_dvd_succ k) dvd_rfl)
  obtain ⟨nB, hB⟩ := colGF_eventuallyPeriodic (p1 := p1) (p3 := p3) h2c h4c (k + 1) dvd_rfl
  refine ⟨max nA nB + p3.natDegree + p4.natDegree, fun M hM => ?_⟩
  exact block_relation (hA.mono (le_max_left _ _)) (hB.mono (le_max_right _ _))
    (colGF_rel h4c k) hM

/-- **The map `ι`.**  The length-`π (k+1)` block of column `k` is its length-`π k` block
repeated `π (k+1) / π k` times. -/
theorem riordan_block_iota (h2 : p2 ≠ 0) (h4 : p4 ≠ 0) (h2c : p2.coeff 0 ≠ 0)
    (h4c : p4.coeff 0 ≠ 0) (k : ℕ) :
    ∃ n0 : ℕ, ∀ M, n0 ≤ M →
      blockPoly (blockPeriod p2 p4 (k + 1)) (colGF p1 p2 p3 p4 k) M
        = blockPoly (blockPeriod p2 p4 k) (colGF p1 p2 p3 p4 k) M
          * ∑ i ∈ Finset.range (blockPeriod p2 p4 (k + 1) / blockPeriod p2 p4 k),
              X ^ (i * blockPeriod p2 p4 k) := by
  obtain ⟨n0, hper⟩ := colGF_eventuallyPeriodic (p1 := p1) (p3 := p3) h2c h4c k dvd_rfl
  refine ⟨n0, fun M hM => ?_⟩
  have hpos : 0 < blockPeriod p2 p4 k := blockPeriod_pos h2 h4 h2c h4c k
  obtain ⟨m, hm⟩ := blockPeriod_dvd_succ (p2 := p2) (p4 := p4) k
  have hdiv : blockPeriod p2 p4 (k + 1) / blockPeriod p2 p4 k = m := by
    rw [hm, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv, hm, mul_comm (blockPeriod p2 p4 k) m]
  exact blockPoly_repeat hper hM m

/-- **`π k` really is the least eventual period of column `k`** when there is no cancellation,
i.e. when the numerator `p₁ p₃ᵏ` and the denominator `p₂ p₄ᵏ` are coprime: every eventual
period of column `k` is a multiple of `π k`. -/
theorem colGF_least_period (h2c : p2.coeff 0 ≠ 0) (h4c : p4.coeff 0 ≠ 0) (k : ℕ)
    (hcop : IsCoprime (colDen p2 p4 k) (p1 * p3 ^ k)) {N n0 : ℕ}
    (hper : EventuallyPeriodic (colGF p1 p2 p3 p4 k) N n0) :
    blockPeriod p2 p4 k ∣ N :=
  polyOrd_dvd_of_eventuallyPeriodic (colGF_spec h2c h4c k) hcop hper

end RiordanF5
