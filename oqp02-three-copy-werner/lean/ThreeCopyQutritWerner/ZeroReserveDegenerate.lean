module

public import ThreeCopyQutritWerner.ZeroReserveEquality

@[expose] public section


/-!
# The complete degenerate-entropy branch at reserve equality

The same product/range argument is made at all three literal physical sites.
A shared zero local entropy yields a thin range at that site. A vanishing
total entropy gives thinness at every site. The positive-entropy branch is
not classified here.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Pure local marginals at site 2 give an actual two-column local range factor. -/
theorem zeroReserve_localRange2_le_two_of_local_purity_one
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hpu : frobSq (ptrace₁₃ (ketBra u u)) = 1)
    (hpv : frobSq (ptrace₁₃ (ketBra v v)) = 1) (z w : ℂ) :
    localRangeDim₂ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  have htrace (q : a × b × c → ℂ) :
      ptraceR (ketBra (q ∘ siteEquiv₂) (q ∘ siteEquiv₂)) =
        ptrace₁₃ (ketBra q q) := by
    ext i j
    simp only [ptraceR, ptrace₁₃, Fintype.sum_prod_type, ketBra,
      Function.comp_apply, siteEquiv₂, Equiv.coe_fn_mk]
  have hru : frobSq (ptraceR (ketBra (u ∘ siteEquiv₂) (u ∘ siteEquiv₂))) = 1 := by
    rw [htrace]
    exact hpu
  have hrv : frobSq (ptraceR (ketBra (v ∘ siteEquiv₂) (v ∘ siteEquiv₂))) = 1 := by
    rw [htrace]
    exact hpv
  obtain ⟨x, p, hx⟩ := zeroReserve_product_of_local_purity_one (u ∘ siteEquiv₂)
    ((vecNormSq_comp_equiv siteEquiv₂ u).trans hu) hru
  obtain ⟨y, q, hy⟩ := zeroReserve_product_of_local_purity_one (v ∘ siteEquiv₂)
    ((vecNormSq_comp_equiv siteEquiv₂ v).trans hv) hrv
  rw [localRangeDim₂_eq_coherentFlatten_rank]
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of (fun i k => ![x i, y i] k),
    Matrix.of (fun k t => ![z * p t.1 * conj (u t.2), w * q t.1 * conj (v t.2)] k), ?_⟩
  ext i t
  simp only [coherentFlatten₂, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, ketBra, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.star_def]
  have hxu : u (t.1.1, i, t.1.2) = x i * p t.1 := hx i t.1
  have hyv : v (t.1.1, i, t.1.2) = y i * q t.1 := hy i t.1
  rw [hxu, hyv]
  ring

/-- Pure local marginals at site 3 give an actual two-column local range factor. -/
theorem zeroReserve_localRange3_le_two_of_local_purity_one
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hpu : frobSq (ptrace₁₂ (ketBra u u)) = 1)
    (hpv : frobSq (ptrace₁₂ (ketBra v v)) = 1) (z w : ℂ) :
    localRangeDim₃ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  have htrace (q : a × b × c → ℂ) :
      ptraceR (ketBra (q ∘ siteEquiv₃) (q ∘ siteEquiv₃)) =
        ptrace₁₂ (ketBra q q) := by
    ext i j
    simp only [ptraceR, ptrace₁₂, Fintype.sum_prod_type, ketBra,
      Function.comp_apply, siteEquiv₃, Equiv.coe_fn_mk]
  have hru : frobSq (ptraceR (ketBra (u ∘ siteEquiv₃) (u ∘ siteEquiv₃))) = 1 := by
    rw [htrace]
    exact hpu
  have hrv : frobSq (ptraceR (ketBra (v ∘ siteEquiv₃) (v ∘ siteEquiv₃))) = 1 := by
    rw [htrace]
    exact hpv
  obtain ⟨x, p, hx⟩ := zeroReserve_product_of_local_purity_one (u ∘ siteEquiv₃)
    ((vecNormSq_comp_equiv siteEquiv₃ u).trans hu) hru
  obtain ⟨y, q, hy⟩ := zeroReserve_product_of_local_purity_one (v ∘ siteEquiv₃)
    ((vecNormSq_comp_equiv siteEquiv₃ v).trans hv) hrv
  rw [localRangeDim₃_eq_coherentFlatten_rank]
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of (fun i k => ![x i, y i] k),
    Matrix.of (fun k t => ![z * p t.1 * conj (u t.2), w * q t.1 * conj (v t.2)] k), ?_⟩
  ext i t
  simp only [coherentFlatten₃, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, ketBra, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.star_def]
  have hxu : u (t.1.1, t.1.2, i) = x i * p t.1 := hx i t.1
  have hyv : v (t.1.1, t.1.2, i) = y i * q t.1 := hy i t.1
  rw [hxu, hyv]
  ring

variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- One degenerate local entropy at a positive-weight reserve zero is enough
for a thin physical source at that same site. -/
theorem zeroReserve_two_ray_eq_zero_thin_of_deficit_zero (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (he : ∃ i, zeroReserveLocalDeficit u i = 0) :
    HasThinLocalRange ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
  obtain ⟨i, hi⟩ := he
  have hv0 := (zeroReserve_two_ray_eq_zero_deficit_zero_iff
    u v hu hv huv lam mu hlam hmu hz i).mp hi
  fin_cases i
  · exact Or.inl (zeroReserve_two_ray_eq_zero_thin_site1 u v hu hv huv lam mu hlam hmu hz hi)
  · refine Or.inr (Or.inl ?_)
    apply zeroReserve_localRange2_le_two_of_local_purity_one u v hu hv
    · change 1 - frobSq (ptrace₁₃ (ketBra u u)) = 0 at hi
      linarith
    · change 1 - frobSq (ptrace₁₃ (ketBra v v)) = 0 at hv0
      linarith
  · refine Or.inr (Or.inr ?_)
    apply zeroReserve_localRange3_le_two_of_local_purity_one u v hu hv
    · change 1 - frobSq (ptrace₁₂ (ketBra u u)) = 0 at hi
      linarith
    · change 1 - frobSq (ptrace₁₂ (ketBra v v)) = 0 at hv0
      linarith

/-- Zero total entropy at a positive-weight reserve zero gives local range
dimension at most two at every physical site. -/
theorem zeroReserve_two_ray_eq_zero_allThin_of_entropy_zero (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (he : zeroReserveLocalEntropy u = 0) :
    localRangeDim₁ ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) ≤ 2 ∧
    localRangeDim₂ ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) ≤ 2 ∧
    localRangeDim₃ ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) ≤ 2 := by
  have hsum : (∑ i, zeroReserveLocalDeficit u i) = 0 :=
    (zeroReserveLocalDeficit_sum u).trans he
  have huFun := (Fintype.sum_eq_zero_iff_of_nonneg
    (zeroReserveLocalDeficit_nonneg u hu)).mp hsum
  have hu0 (i : Fin 3) : zeroReserveLocalDeficit u i = 0 := congrFun huFun i
  have hv0 (i : Fin 3) := (zeroReserve_two_ray_eq_zero_deficit_zero_iff
    u v hu hv huv lam mu hlam hmu hz i).mp (hu0 i)
  refine ⟨zeroReserve_two_ray_eq_zero_thin_site1 u v hu hv huv lam mu hlam hmu hz (hu0 0), ?_, ?_⟩
  · apply zeroReserve_localRange2_le_two_of_local_purity_one u v hu hv
    · have h := hu0 1
      change 1 - frobSq (ptrace₁₃ (ketBra u u)) = 0 at h
      linarith
    · have h := hv0 1
      change 1 - frobSq (ptrace₁₃ (ketBra v v)) = 0 at h
      linarith
  · apply zeroReserve_localRange3_le_two_of_local_purity_one u v hu hv
    · have h := hu0 2
      change 1 - frobSq (ptrace₁₂ (ketBra u u)) = 0 at h
      linarith
    · have h := hv0 2
      change 1 - frobSq (ptrace₁₂ (ketBra v v)) = 0 at h
      linarith

end ThreeCopyQutritWerner
