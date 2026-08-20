import RequestProject.Periods

/-!
# The explicit formula for the order of a polynomial over `F₅`

If `Q = ∏ φ_j ^ m_j` with the `φ_j` pairwise non-associated irreducibles, `φ_j(0) ≠ 0` and
`m_j ≥ 1`, then

  `ord Q = lcm_j ( ord(φ_j) · 5 ^ ⌈log₅ m_j⌉ ) = E · 5 ^ (max_j ⌈log₅ m_j⌉)`,
  `E = lcm_j ord(φ_j)`.

Applied to the Riordan denominator `Q k = p₂ p₄ᵏ = ∏ φ_j ^ (a_j + k b_j)` this is the formula
`π k = E · 5 ^ s_k`, `s_k = max_j ⌈log₅ (a_j + k b_j)⌉`.
-/

open Polynomial

namespace RiordanF5

theorem polyOrd_one : polyOrd (1 : F5[X]) = 1 :=
  Nat.dvd_one.mp ((polyOrd_dvd_iff 1 1).mpr (one_dvd _))

/-- The order of a product of coprime polynomials is the lcm of the orders. -/
theorem polyOrd_mul_of_coprime {Q1 Q2 : F5[X]} (h : IsCoprime Q1 Q2) :
    polyOrd (Q1 * Q2) = Nat.lcm (polyOrd Q1) (polyOrd Q2) := by
  have key : ∀ N, polyOrd (Q1 * Q2) ∣ N ↔ Nat.lcm (polyOrd Q1) (polyOrd Q2) ∣ N := by
    intro N
    rw [polyOrd_dvd_iff, Nat.lcm_dvd_iff, polyOrd_dvd_iff, polyOrd_dvd_iff]
    constructor
    · intro hd
      exact ⟨dvd_trans (dvd_mul_right Q1 Q2) hd, dvd_trans (dvd_mul_left Q2 Q1) hd⟩
    · rintro ⟨h1, h2⟩
      exact h.mul_dvd h1 h2
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

/-- The order of an irreducible polynomial `≠ t` is prime to `5`. -/
theorem not_five_dvd_polyOrd {f : F5[X]} (hirr : Irreducible f) (h0 : f.coeff 0 ≠ 0) :
    ¬ (5 ∣ polyOrd f) := by
  rintro ⟨e, he⟩
  have hpos : 0 < polyOrd f := polyOrd_pos hirr.ne_zero h0
  have hepos : 0 < e := by omega
  have hdvd : f ∣ ((X : F5[X]) ^ e - 1) ^ 5 := by
    rw [X_pow_sub_one_pow_five, ← he]
    exact polyOrd_dvd_self f
  have hd2 : f ∣ (X : F5[X]) ^ e - 1 := hirr.prime.dvd_of_dvd_pow hdvd
  have hdd : polyOrd f ∣ e := (polyOrd_dvd_iff f e).mpr hd2
  have := Nat.le_of_dvd hepos hdd
  omega

/-- Iterated Frobenius: `(tᴺ - 1)^{5ʲ} = t^{N·5ʲ} - 1`. -/
theorem X_pow_sub_one_pow_five_pow (N j : ℕ) :
    ((X : F5[X]) ^ N - 1) ^ (5 ^ j) = (X : F5[X]) ^ (N * 5 ^ j) - 1 := by
  induction j with
  | zero => simp
  | succ i ih =>
    have h : (5 : ℕ) ^ (i + 1) = 5 ^ i * 5 := by ring
    rw [h, pow_mul, ih, X_pow_sub_one_pow_five]
    congr 2
    ring

/-- If `p` is prime, `p² ∤ g` and `pᵐ ∣ gⁿ`, then `m ≤ n`. -/
theorem le_of_pow_dvd_pow_of_sq_not_dvd {R : Type*} [CommRing R] [IsDomain R] {p g : R}
    (hp : Prime p) (hg2 : ¬ p ^ 2 ∣ g) {m n : ℕ} (h : p ^ m ∣ g ^ n) : m ≤ n := by
  by_cases hpg : p ∣ g
  · obtain ⟨c, hc⟩ := hpg
    have hpc : ¬ p ∣ c := by
      rintro ⟨d, hd⟩
      exact hg2 ⟨d, by rw [hc, hd]; ring⟩
    by_contra hmn
    push_neg at hmn
    have h1 : p ^ (n + 1) ∣ g ^ n := dvd_trans (pow_dvd_pow p (by omega)) h
    rw [hc, mul_pow] at h1
    have h2 : p ^ n * p ∣ p ^ n * c ^ n := by rw [← pow_succ]; exact h1
    have h3 : p ∣ c ^ n := (mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp h2
    exact hpc (hp.dvd_of_dvd_pow h3)
  · by_contra hm
    push_neg at hm
    exact hpg (hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p (by omega)) h))

/-- `tᵉ - 1` is squarefree at every irreducible factor, provided `5 ∤ e`. -/
theorem sq_not_dvd_X_pow_sub_one {f : F5[X]} (hirr : Irreducible f) (h0 : f.coeff 0 ≠ 0) {e : ℕ}
    (h5 : ¬ (5 ∣ e)) : ¬ (f ^ 2 ∣ (X : F5[X]) ^ e - 1) := by
  rintro ⟨h, hh⟩
  have hder : Polynomial.derivative ((X : F5[X]) ^ e - 1) = C ((e : F5)) * X ^ (e - 1) := by
    simp [Polynomial.derivative_X_pow]
  have hfd : f ∣ Polynomial.derivative ((X : F5[X]) ^ e - 1) := by
    rw [hh, Polynomial.derivative_mul]
    have hd2 : Polynomial.derivative (f ^ 2) = C 2 * f * Polynomial.derivative f := by
      rw [Polynomial.derivative_pow]
      norm_num
    rw [hd2]
    exact dvd_add ⟨C 2 * Polynomial.derivative f * h, by ring⟩
      ⟨f * Polynomial.derivative h, by ring⟩
  rw [hder] at hfd
  have hEne : ((e : F5)) ≠ 0 := fun hE => h5 (Fin.natCast_eq_zero.mp hE)
  have hunit : IsUnit (C ((e : F5))) := Polynomial.isUnit_C.mpr hEne.isUnit
  have hfX : f ∣ (X : F5[X]) ^ (e - 1) := (IsUnit.dvd_mul_left hunit).mp hfd
  rcases Nat.eq_zero_or_pos (e - 1) with h1 | h1
  · rw [h1, pow_zero] at hfX
    exact hirr.not_isUnit (isUnit_of_dvd_one hfX)
  · have hfXd : f ∣ (X : F5[X]) := hirr.prime.dvd_of_dvd_pow hfX
    have hassoc := hirr.associated_of_dvd Polynomial.irreducible_X hfXd
    exact h0 (Polynomial.X_dvd_iff.mp hassoc.symm.dvd)

/-- **Order of a prime power.** For `f` irreducible with `f(0) ≠ 0` and `m ≥ 1`,
`ord (f ^ m) = ord f · 5 ^ ⌈log₅ m⌉`. -/
theorem polyOrd_pow_irreducible {f : F5[X]} (hirr : Irreducible f) (h0 : f.coeff 0 ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) :
    polyOrd (f ^ m) = polyOrd f * 5 ^ Nat.clog 5 m := by
  set e := polyOrd f with he
  set j := Nat.clog 5 m with hjdef
  have hepos : 0 < e := polyOrd_pos hirr.ne_zero h0
  have h5e : ¬ (5 ∣ e) := not_five_dvd_polyOrd hirr h0
  have hfg : f ∣ (X : F5[X]) ^ e - 1 := polyOrd_dvd_self f
  have hsq : ¬ (f ^ 2 ∣ (X : F5[X]) ^ e - 1) := sq_not_dvd_X_pow_sub_one hirr h0 h5e
  have hmle : m ≤ 5 ^ j := Nat.le_pow_clog (by norm_num) m
  have hup : polyOrd (f ^ m) ∣ e * 5 ^ j := by
    rw [polyOrd_dvd_iff, ← X_pow_sub_one_pow_five_pow]
    exact dvd_trans (pow_dvd_pow f hmle) (pow_dvd_pow_of_dvd hfg _)
  have hlow : e ∣ polyOrd (f ^ m) := by
    rw [he, polyOrd_dvd_iff]
    exact dvd_trans (dvd_pow_self f (by omega)) (polyOrd_dvd_self (f ^ m))
  obtain ⟨d, hd⟩ := hlow
  have hdvd5 : d ∣ 5 ^ j := by
    have h' : e * d ∣ e * 5 ^ j := hd ▸ hup
    exact (Nat.mul_dvd_mul_iff_left hepos).mp h'
  obtain ⟨v, hv, hdv⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hdvd5
  have hfm : f ^ m ∣ ((X : F5[X]) ^ e - 1) ^ (5 ^ v) := by
    rw [X_pow_sub_one_pow_five_pow]
    have hpe : polyOrd (f ^ m) = e * 5 ^ v := by rw [hd, hdv]
    rw [← hpe]
    exact polyOrd_dvd_self _
  have hmv : m ≤ 5 ^ v := le_of_pow_dvd_pow_of_sq_not_dvd hirr.prime hsq hfm
  have hjv : j ≤ v := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hmv
  have hvj : v = j := le_antisymm hv hjv
  rw [hd, hdv, hvj]

/-- **The general order formula.** For a product of powers of pairwise non-associated
irreducibles with nonzero constant term, the order is the lcm of the orders of the factors. -/
theorem polyOrd_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → F5[X]) (m : ι → ℕ)
    (hirr : ∀ i ∈ s, Irreducible (f i)) (h0 : ∀ i ∈ s, (f i).coeff 0 ≠ 0)
    (hm : ∀ i ∈ s, 1 ≤ m i)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (f i) (f j)) :
    polyOrd (∏ i ∈ s, f i ^ m i) = s.lcm (fun i => polyOrd (f i) * 5 ^ Nat.clog 5 (m i)) := by
  induction s using Finset.induction with
  | empty => simpa using polyOrd_one
  | insert a s ha ih =>
    have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hamem : a ∈ insert a s := Finset.mem_insert_self a s
    have hcop : IsCoprime (f a ^ m a) (∏ i ∈ s, f i ^ m i) := by
      refine IsCoprime.pow_left (IsCoprime.prod_right (fun i hi => IsCoprime.pow_right ?_))
      refine ((hirr a hamem).coprime_iff_not_dvd).mpr (fun hdvd => ?_)
      exact hdist a hamem i (hmem i hi) (fun h => ha (h ▸ hi))
        ((hirr a hamem).associated_of_dvd (hirr i (hmem i hi)) hdvd)
    rw [Finset.prod_insert ha, polyOrd_mul_of_coprime hcop,
      polyOrd_pow_irreducible (hirr a hamem) (h0 a hamem) (hm a hamem),
      ih (fun i hi => hirr i (hmem i hi)) (fun i hi => h0 i (hmem i hi))
        (fun i hi => hm i (hmem i hi))
        (fun i hi j hj hij => hdist i (hmem i hi) j (hmem j hj) hij),
      Finset.lcm_insert]
    rfl

/-- **The formula for the periods of a rational Riordan array.**
If `p₂ = ∏ φ_j^{a_j}` and `p₄ = ∏ φ_j^{b_j}` over a common set of pairwise non-associated
irreducibles with nonzero constant term, then the least eventual period of column `k` is
`π k = lcm_j ( e_j · 5 ^ ⌈log₅ (a_j + k b_j)⌉ )` where `e_j = ord φ_j`. -/
theorem blockPeriod_formula {ι : Type*} [DecidableEq ι] {p2 p4 : F5[X]} (s : Finset ι)
    (f : ι → F5[X]) (a b : ι → ℕ) (k : ℕ)
    (hirr : ∀ i ∈ s, Irreducible (f i)) (h0 : ∀ i ∈ s, (f i).coeff 0 ≠ 0)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (f i) (f j))
    (hab : ∀ i ∈ s, 1 ≤ a i + k * b i)
    (hp2 : p2 = ∏ i ∈ s, f i ^ a i) (hp4 : p4 = ∏ i ∈ s, f i ^ b i) :
    blockPeriod p2 p4 k
      = s.lcm (fun i => polyOrd (f i) * 5 ^ Nat.clog 5 (a i + k * b i)) := by
  have hQ : colDen p2 p4 k = ∏ i ∈ s, f i ^ (a i + k * b i) := by
    rw [colDen, hp2, hp4, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← pow_mul, ← pow_add, mul_comm (b i) k]
  rw [blockPeriod, hQ]
  exact polyOrd_prod s f (fun i => a i + k * b i) hirr h0 hab hdist

/-- The lcm of numbers prime to `5` is prime to `5`. -/
theorem not_five_dvd_lcm {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, ¬ (5 ∣ e i)) : ¬ (5 ∣ s.lcm e) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.lcm_insert]
    intro hdvd
    have hlcm : (lcm (e a) (s.lcm e) : ℕ) ∣ e a * s.lcm e := Nat.lcm_dvd_mul _ _
    have h5 : (5 : ℕ) ∣ e a * s.lcm e := dvd_trans hdvd hlcm
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h5 with h | h
    · exact he a (Finset.mem_insert_self a s) h
    · exact ih (fun i hi => he i (Finset.mem_insert_of_mem hi)) h

/-- Repackaging: `lcm_j (e_j 5^{u_j}) = (lcm_j e_j) · 5 ^ (max_j u_j)` when every `e_j` is
prime to `5`. -/
theorem lcm_mul_pow_five {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℕ) (u : ι → ℕ) (he : ∀ i ∈ s, ¬ (5 ∣ e i)) :
    s.lcm (fun i => e i * 5 ^ u i) = (s.lcm e) * 5 ^ (s.sup u) := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine Finset.lcm_dvd (fun i hi => ?_)
    exact mul_dvd_mul (Finset.dvd_lcm hi) (pow_dvd_pow 5 (Finset.le_sup hi))
  · have hE : s.lcm e ∣ s.lcm (fun i => e i * 5 ^ u i) :=
      Finset.lcm_dvd (fun i hi => dvd_trans (dvd_mul_right (e i) (5 ^ u i)) (Finset.dvd_lcm hi))
    obtain ⟨i0, hi0, hsup⟩ := Finset.exists_mem_eq_sup s hs u
    have hP : (5 : ℕ) ^ (s.sup u) ∣ s.lcm (fun i => e i * 5 ^ u i) := by
      rw [hsup]
      exact dvd_trans (dvd_mul_left (5 ^ u i0) (e i0)) (Finset.dvd_lcm hi0)
    have hcop : Nat.Coprime (s.lcm e) (5 ^ s.sup u) :=
      Nat.Coprime.pow_right _
        (((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (not_five_dvd_lcm s e he)).symm)
    exact hcop.mul_dvd_of_dvd_of_dvd hE hP

/-- **The periods as a `5`-adic tower.**  Under the same hypotheses,
`π k = E · 5 ^ s_k` with `E = lcm_j ord(φ_j)` and `s_k = max_j ⌈log₅ (a_j + k b_j)⌉`. -/
theorem blockPeriod_formula_tower {ι : Type*} [DecidableEq ι] {p2 p4 : F5[X]} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → F5[X]) (a b : ι → ℕ) (k : ℕ)
    (hirr : ∀ i ∈ s, Irreducible (f i)) (h0 : ∀ i ∈ s, (f i).coeff 0 ≠ 0)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (f i) (f j))
    (hab : ∀ i ∈ s, 1 ≤ a i + k * b i)
    (hp2 : p2 = ∏ i ∈ s, f i ^ a i) (hp4 : p4 = ∏ i ∈ s, f i ^ b i) :
    blockPeriod p2 p4 k
      = (s.lcm (fun i => polyOrd (f i)))
          * 5 ^ (s.sup (fun i => Nat.clog 5 (a i + k * b i))) := by
  rw [blockPeriod_formula s f a b k hirr h0 hdist hab hp2 hp4]
  exact lcm_mul_pow_five s hs (fun i => polyOrd (f i))
    (fun i => Nat.clog 5 (a i + k * b i))
    (fun i hi => not_five_dvd_polyOrd (hirr i hi) (h0 i hi))

end RiordanF5
