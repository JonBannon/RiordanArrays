import RequestProject.Periods

/-!
# Periodic blocks and the circulant relation

A power series `H` over `F₅` whose coefficient sequence is eventually `N`-periodic has, for
every sufficiently large starting index `M`, a *periodic block*

  `B = ∑_{r<N} c(M+r) tʳ ∈ F₅[t]/(tᴺ - 1)`,

an element of the circulant ring `Cyc N = F₅[t]/(tᴺ-1)`; multiplication by `t` there is the
cyclic shift `S_N`.

The two main results are:

* `block_mul_poly` : reading off the block intertwines multiplication by a polynomial with
  the corresponding circulant, `block (P·H) = P(S_N) · block H`;
* `block_relation` : if `p₄ B = p₃ A` as power series, then the blocks satisfy
  `p₄(S_N) · C_B = p₃(S_N) · C_A`.

We also record `blockPoly_repeat`, which identifies the length-`mn` block of an
`n`-periodic series with the `n`-block repeated `m` times (the map `ι` of the statement).
-/

open Polynomial

namespace RiordanF5

/-- The coefficient sequence of `H` is `N`-periodic from index `n0` on. -/
def EventuallyPeriodic (H : PowerSeries F5) (N n0 : ℕ) : Prop :=
  ∀ n, n0 ≤ n → PowerSeries.coeff (n + N) H = PowerSeries.coeff n H

/-- The length-`N` block of `H` starting at position `M`, as a polynomial. -/
noncomputable def blockPoly (N : ℕ) (H : PowerSeries F5) (M : ℕ) : F5[X] :=
  ∑ r ∈ Finset.range N, C (PowerSeries.coeff (M + r) H) * X ^ r

/-- The ring of `N`-periodic blocks, `F₅[t]/(tᴺ - 1)`.  Multiplication by the class of `t`
is the cyclic shift `S_N`, so this is the ring of circulants of size `N`. -/
abbrev Cyc (N : ℕ) := AdjoinRoot ((X : F5[X]) ^ N - 1)

/-- The periodic block of `H` of length `N` read from position `M`, as an element of
the circulant ring `F₅[t]/(tᴺ-1)`. -/
noncomputable def block (N : ℕ) (H : PowerSeries F5) (M : ℕ) : Cyc N :=
  AdjoinRoot.mk _ (blockPoly N H M)

/-- In `Cyc N` the shift satisfies `Sᴺ = 1`. -/
theorem root_pow_N (N : ℕ) : (AdjoinRoot.root ((X : F5[X]) ^ N - 1)) ^ N = 1 := by
  have h : (AdjoinRoot.mk ((X : F5[X]) ^ N - 1)) ((X : F5[X]) ^ N - 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
  exact h

theorem mk_X_pow_sub_one (N : ℕ) :
    (AdjoinRoot.mk ((X : F5[X]) ^ N - 1)) ((X : F5[X]) ^ N - 1) = 0 := AdjoinRoot.mk_self

/-- A power series with polynomial numerator and denominator `Q`, where `Q ∣ tᴺ - 1`,
has eventually `N`-periodic coefficients. -/
theorem eventuallyPeriodic_of_den {P Q : F5[X]} {H : PowerSeries F5} {N : ℕ}
    (hH : (Q : PowerSeries F5) * H = (P : PowerSeries F5))
    (hdvd : Q ∣ (X : F5[X]) ^ N - 1) :
    ∃ n0, EventuallyPeriodic H N n0 := by
  obtain ⟨R, hR⟩ := hdvd
  refine ⟨(R * P).natDegree + 1, ?_⟩
  intro n hn
  have key : ((((X : F5[X]) ^ N - 1 : F5[X])) : PowerSeries F5) * H
      = ((R * P : F5[X]) : PowerSeries F5) := by
    rw [hR]
    push_cast
    calc (Q : PowerSeries F5) * (R : PowerSeries F5) * H
        = (R : PowerSeries F5) * ((Q : PowerSeries F5) * H) := by ring
      _ = (R : PowerSeries F5) * (P : PowerSeries F5) := by rw [hH]
  have h1 : PowerSeries.coeff (n + N) (((((X : F5[X]) ^ N - 1 : F5[X])) : PowerSeries F5) * H)
      = PowerSeries.coeff n H - PowerSeries.coeff (n + N) H := by
    push_cast
    rw [sub_mul, one_mul, map_sub, mul_comm]
    congr 1
    exact PowerSeries.coeff_mul_X_pow H N n
  rw [key, Polynomial.coeff_coe] at h1
  have h2 : (R * P).coeff (n + N) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h2] at h1
  exact (sub_eq_zero.mp h1.symm).symm

/-- An eventually `N`-periodic series becomes a polynomial after multiplication by `tᴺ - 1`. -/
theorem exists_poly_of_eventuallyPeriodic {H : PowerSeries F5} {N n0 : ℕ}
    (hper : EventuallyPeriodic H N n0) :
    ∃ S : F5[X], (((X : F5[X]) ^ N - 1 : F5[X]) : PowerSeries F5) * H = (S : PowerSeries F5) := by
  set T := (((X : F5[X]) ^ N - 1 : F5[X]) : PowerSeries F5) * H with hT
  have hvanish : ∀ m, n0 + N ≤ m → PowerSeries.coeff m T = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + N := ⟨m - N, by omega⟩
    have hcalc : PowerSeries.coeff (n + N) T
        = PowerSeries.coeff n H - PowerSeries.coeff (n + N) H := by
      rw [hT]
      push_cast
      rw [sub_mul, one_mul, map_sub, mul_comm]
      congr 1
      exact PowerSeries.coeff_mul_X_pow H N n
    rw [hcalc, hper n (by omega), sub_self]
  refine ⟨PowerSeries.trunc (n0 + N) T, ?_⟩
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases h : m < n0 + N
  · rw [if_pos h]
  · rw [if_neg h, hvanish m (by omega)]

/-- **Minimality of the period.**  If the fraction `P/Q` is in lowest terms, then every
eventual period of its coefficient sequence is a multiple of `ord Q`; so `ord Q` is the least
eventual period. -/
theorem polyOrd_dvd_of_eventuallyPeriodic {P Q : F5[X]} {H : PowerSeries F5}
    (hH : (Q : PowerSeries F5) * H = (P : PowerSeries F5)) (hcop : IsCoprime Q P)
    {N n0 : ℕ} (hper : EventuallyPeriodic H N n0) : polyOrd Q ∣ N := by
  obtain ⟨S, hS⟩ := exists_poly_of_eventuallyPeriodic hper
  have hpoly : ((X : F5[X]) ^ N - 1) * P = Q * S := by
    apply Polynomial.coe_injective F5
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hS, ← hH]
    ring
  rw [polyOrd_dvd_iff]
  exact hcop.dvd_of_dvd_mul_right ⟨S, hpoly⟩

/-- Periodicity with an arbitrary number of periods. -/
theorem EventuallyPeriodic.iterate {H : PowerSeries F5} {N n0 : ℕ}
    (hper : EventuallyPeriodic H N n0) (q : ℕ) {n : ℕ} (hn : n0 ≤ n) :
    PowerSeries.coeff (n + q * N) H = PowerSeries.coeff n H := by
  induction q with
  | zero => simp
  | succ m ih =>
    have : n + (m + 1) * N = (n + m * N) + N := by ring
    rw [this, hper _ (by omega), ih]

/-- The polynomial shift identity underlying the cyclic-shift description of blocks. -/
theorem blockPoly_shift {H : PowerSeries F5} {N n0 M : ℕ} (hper : EventuallyPeriodic H N n0)
    (hM : n0 ≤ M) :
    X * blockPoly N H (M + 1)
      = blockPoly N H M + C (PowerSeries.coeff M H) * ((X : F5[X]) ^ N - 1) := by
  set f : ℕ → F5[X] := fun s => C (PowerSeries.coeff (M + s) H) * X ^ s with hf
  have hL : X * blockPoly N H (M + 1) = ∑ r ∈ Finset.range N, f (r + 1) := by
    rw [blockPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [hf]
    ring_nf
  have h2 : ∑ i ∈ Finset.range (N + 1), f i = (∑ r ∈ Finset.range N, f (r + 1)) + f 0 :=
    Finset.sum_range_succ' f N
  have h3 : ∑ i ∈ Finset.range (N + 1), f i = (∑ i ∈ Finset.range N, f i) + f N :=
    Finset.sum_range_succ f N
  have hfN : f N = C (PowerSeries.coeff M H) * X ^ N := by
    simp only [hf]
    rw [hper M hM]
  have hf0 : f 0 = C (PowerSeries.coeff M H) := by simp [hf]
  have hsum : (∑ r ∈ Finset.range N, f (r + 1)) = (∑ i ∈ Finset.range N, f i) + f N - f 0 := by
    rw [← h3, h2]; ring
  rw [hL, hsum, hfN, hf0]
  simp only [blockPoly, hf]
  ring

/-- Moving the reading position one step to the right is the cyclic shift. -/
theorem block_shift {H : PowerSeries F5} {N n0 M : ℕ} (hper : EventuallyPeriodic H N n0)
    (hM : n0 ≤ M) :
    block N H M = AdjoinRoot.root _ * block N H (M + 1) := by
  have := congrArg (AdjoinRoot.mk ((X : F5[X]) ^ N - 1)) (blockPoly_shift hper hM)
  rw [map_mul, map_add, map_mul, mk_X_pow_sub_one, mul_zero, add_zero,
    AdjoinRoot.mk_X] at this
  exact this.symm

theorem block_shift_pow {H : PowerSeries F5} {N n0 M : ℕ} (hper : EventuallyPeriodic H N n0)
    (hM : n0 ≤ M) (i : ℕ) :
    block N H M = (AdjoinRoot.root _) ^ i * block N H (M + i) := by
  induction i with
  | zero => simp
  | succ j ih =>
    rw [ih, block_shift hper (show n0 ≤ M + j by omega)]
    rw [show M + j + 1 = M + (j + 1) by ring]
    ring

/-- Blocks are additive in the series. -/
theorem blockPoly_add (N : ℕ) (H1 H2 : PowerSeries F5) (M : ℕ) :
    blockPoly N (H1 + H2) M = blockPoly N H1 M + blockPoly N H2 M := by
  simp only [blockPoly, map_add, map_add, add_mul, Finset.sum_add_distrib]

theorem blockPoly_sum {ι : Type*} (N : ℕ) (s : Finset ι) (G : ι → PowerSeries F5) (M : ℕ) :
    blockPoly N (∑ i ∈ s, G i) M = ∑ i ∈ s, blockPoly N (G i) M := by
  classical
  induction s using Finset.induction with
  | empty => simp [blockPoly]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, blockPoly_add, ih]

/-- Multiplying by a monomial `a·tⁱ` shifts the reading position by `i`. -/
theorem blockPoly_monomial_mul {H : PowerSeries F5} {N M i : ℕ} (a : F5) (hi : i ≤ M) :
    blockPoly N (((monomial i a : F5[X]) : PowerSeries F5) * H) M
      = C a * blockPoly N H (M - i) := by
  simp only [blockPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hco : PowerSeries.coeff (M + r) (((monomial i a : F5[X]) : PowerSeries F5) * H)
      = a * PowerSeries.coeff (M - i + r) H := by
    have hcoe : ((monomial i a : F5[X]) : PowerSeries F5)
        = PowerSeries.C a * PowerSeries.X ^ i := by
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_mk]
      ext n
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    have hidx : M + r = (M - i + r) + i := by omega
    have hcomm : PowerSeries.C a * PowerSeries.X ^ i * H
        = PowerSeries.X ^ i * (PowerSeries.C a * H) := by ring
    rw [hcoe, hidx, hcomm, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_C_mul]
  rw [hco, map_mul]
  ring

/-- Reading off blocks intertwines multiplication by a polynomial with the corresponding
circulant `P(S_N)`. -/
theorem block_mul_poly {H : PowerSeries F5} {N n0 M : ℕ} (hper : EventuallyPeriodic H N n0)
    (P : F5[X]) (hM : n0 + P.natDegree ≤ M) :
    block N ((P : PowerSeries F5) * H) M = AdjoinRoot.mk _ P * block N H M := by
  classical
  set D := P.natDegree with hD
  have hPsum : P = ∑ i ∈ Finset.range (D + 1), monomial i (P.coeff i) :=
    Polynomial.as_sum_range' P (D + 1) (by omega)
  have hcoe : (P : PowerSeries F5) * H
      = ∑ i ∈ Finset.range (D + 1), ((monomial i (P.coeff i) : F5[X]) : PowerSeries F5) * H := by
    rw [← Finset.sum_mul]
    congr 1
    have hs := map_sum (Polynomial.coeToPowerSeries.ringHom (R := F5))
      (fun i => monomial i (P.coeff i)) (Finset.range (D + 1))
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hs
    conv_lhs => rw [hPsum]
    exact hs
  rw [block, hcoe, blockPoly_sum]
  rw [map_sum]
  have hterm : ∀ i ∈ Finset.range (D + 1),
      AdjoinRoot.mk ((X : F5[X]) ^ N - 1)
          (blockPoly N (((monomial i (P.coeff i) : F5[X]) : PowerSeries F5) * H) M)
        = AdjoinRoot.mk _ (monomial i (P.coeff i)) * block N H M := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hiM : i ≤ M := by omega
    rw [blockPoly_monomial_mul _ hiM, map_mul]
    have hshift : block N H (M - i) = (AdjoinRoot.root ((X : F5[X]) ^ N - 1)) ^ i
        * block N H M := by
      have := block_shift_pow hper (show n0 ≤ M - i by omega) i
      rwa [show M - i + i = M by omega] at this
    have hb : (AdjoinRoot.mk ((X : F5[X]) ^ N - 1)) (blockPoly N H (M - i))
        = block N H (M - i) := rfl
    rw [hb, hshift, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← hPsum]

/-- **The circulant relation between neighbouring blocks.**
If `p₄ · B = p₃ · A` as power series and both coefficient sequences are eventually
`N`-periodic, then their periodic blocks satisfy `p₄(S_N) C_B = p₃(S_N) C_A`
in `F₅[t]/(tᴺ-1)`. -/
theorem block_relation {A B : PowerSeries F5} {p3 p4 : F5[X]} {N n0 M : ℕ}
    (hA : EventuallyPeriodic A N n0) (hB : EventuallyPeriodic B N n0)
    (h : (p4 : PowerSeries F5) * B = (p3 : PowerSeries F5) * A)
    (hM : n0 + p3.natDegree + p4.natDegree ≤ M) :
    AdjoinRoot.mk _ p4 * block N B M = AdjoinRoot.mk _ p3 * block N A M := by
  rw [← block_mul_poly hB p4 (by omega), ← block_mul_poly hA p3 (by omega), h]

/-- **The circulant `p(S_N)` is singular whenever `p` is a nonconstant divisor of `tᴺ - 1`.**
This is why the block relation is an equation rather than a map: one cannot invert `p₄(S_N)`. -/
theorem mk_not_isUnit_of_dvd {p : F5[X]} {N : ℕ} (hN : 0 < N) (hdvd : p ∣ (X : F5[X]) ^ N - 1)
    (hdeg : 0 < p.natDegree) : ¬ IsUnit (AdjoinRoot.mk ((X : F5[X]) ^ N - 1) p) := by
  obtain ⟨R, hR⟩ := hdvd
  have hXN : ((X : F5[X]) ^ N - 1).natDegree = N := by
    compute_degree!
    rw [if_neg hN.ne']
    decide
  have hXNne : ((X : F5[X]) ^ N - 1) ≠ 0 := by
    intro h
    rw [h] at hXN
    simp at hXN
    omega
  have hpne : p ≠ 0 := by rintro rfl; rw [zero_mul] at hR; exact hXNne hR
  have hRne : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hXNne hR
  have hdegs : p.natDegree + R.natDegree = N := by
    rw [← hXN, hR, Polynomial.natDegree_mul hpne hRne]
  have hmkR : AdjoinRoot.mk ((X : F5[X]) ^ N - 1) R ≠ 0 := by
    rw [Ne, AdjoinRoot.mk_eq_zero]
    intro hd
    have := Polynomial.natDegree_le_of_dvd hd hRne
    rw [hXN] at this
    omega
  intro hunit
  have hzero : AdjoinRoot.mk ((X : F5[X]) ^ N - 1) p * AdjoinRoot.mk _ R = 0 := by
    rw [← map_mul, ← hR, AdjoinRoot.mk_self]
  exact hmkR (hunit.mul_right_eq_zero.mp hzero)

/-- **The repetition map `ι`.**  If `H` is eventually `n`-periodic, its length-`m·n` block is
the length-`n` block repeated `m` times. -/
theorem blockPoly_repeat {H : PowerSeries F5} {n n0 M : ℕ} (hper : EventuallyPeriodic H n n0)
    (hM : n0 ≤ M) (m : ℕ) :
    blockPoly (m * n) H M = blockPoly n H M * ∑ i ∈ Finset.range m, X ^ (i * n) := by
  induction m with
  | zero => simp [blockPoly]
  | succ q ih =>
    have hsplit : blockPoly ((q + 1) * n) H M
        = blockPoly (q * n) H M
          + ∑ j ∈ Finset.range n, C (PowerSeries.coeff (M + (q * n + j)) H) * X ^ (q * n + j) := by
      simp only [blockPoly, show (q + 1) * n = q * n + n by ring]
      rw [Finset.sum_range_add]
    have hlast : (∑ j ∈ Finset.range n, C (PowerSeries.coeff (M + (q * n + j)) H)
          * X ^ (q * n + j))
        = X ^ (q * n) * blockPoly n H M := by
      rw [blockPoly, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have : PowerSeries.coeff (M + (q * n + j)) H = PowerSeries.coeff (M + j) H := by
        have h1 : M + (q * n + j) = (M + j) + q * n := by ring
        rw [h1, hper.iterate q (show n0 ≤ M + j by omega)]
      rw [this, pow_add]
      ring
    rw [hsplit, hlast, ih, Finset.sum_range_succ]
    ring

end RiordanF5
