module

public import ThreeCopyQutritWerner.NuclearTraceCompound
public import ThreeCopyQutritWerner.TwoCutIdentity
public import ThreeCopyQutritWerner.TwoCutTransport

@[expose] public section


/-!
# Reduced transitions at the literal three manuscript cuts

The exterior-square transition estimate is transported to the manuscript's
unnormalized partial traces, with no assumption on a transition's rank. The
left-traced transition has squared Frobenius norm equal to the complementary
pure-state reduction pairing. For orthogonal rays its ordinary trace vanishes.

These are the contraction and normalization steps of Wu--Zou Lemma 5.1 and
Section 6. The sharp complementary partial-trace inequality, the resulting
positive rank-two reserve, and equality classification are not asserted here.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Flatten a bipartite ray with the retained subsystem indexing matrix rows. -/
def zeroReserveCutFlatten {L R : Type*} (u : L × R → ℂ) : Matrix R L ℂ :=
  fun r l => u (l, r)

section Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]

/-- The literal partial trace is a product of the two cut flattenings. -/
theorem zeroReserveCutFlatten_transition (u v : L × R → ℂ) :
    ptraceL (ketBra u v) = zeroReserveCutFlatten u * (zeroReserveCutFlatten v)ᴴ := by
  ext r s
  simp only [ptraceL, ketBra, zeroReserveCutFlatten, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def]

/-- The other Gram matrix is the transpose of the complementary reduction. -/
theorem zeroReserveCutFlatten_gram (u : L × R → ℂ) :
    (zeroReserveCutFlatten u)ᴴ * zeroReserveCutFlatten u =
      (ptraceR (ketBra u u))ᵀ := by
  ext l k
  simp only [zeroReserveCutFlatten, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Matrix.transpose_apply, ptraceR, ketBra]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem zeroReserveCutFlatten_frobSq (u : L × R → ℂ) :
    frobSq (zeroReserveCutFlatten u) = vecNormSq u := by
  simp only [frobSq, zeroReserveCutFlatten, vecNormSq, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem zeroReserveTransition_frobSq_transpose {m n : Type*}
    [Fintype m] [Fintype n] (X : Matrix m n ℂ) : frobSq Xᵀ = frobSq X := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Nonnegativity of the actual complementary purity defect. -/
theorem zeroReserveTransition_purity_defect_nonneg (u : L × R → ℂ) :
    0 ≤ vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)) := by
  have h := zeroReserve_gram_defect_nonneg (zeroReserveCutFlatten u)
  simpa only [zeroReserveCutFlatten_frobSq, zeroReserveCutFlatten_gram,
    zeroReserveTransition_frobSq_transpose] using h

/-- Exterior transition bound in literal partial-trace notation, without normalizing the rays. -/
theorem zeroReserveTransition_defect_le [DecidableEq R] (u v : L × R → ℂ) :
    nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) ≤
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))) := by
  have h := nuclearTrace_transition_defect_le (zeroReserveCutFlatten u)
    (zeroReserveCutFlatten v)
  simpa only [← zeroReserveCutFlatten_transition, zeroReserveCutFlatten_frobSq,
    zeroReserveCutFlatten_gram, zeroReserveTransition_frobSq_transpose] using h

/-- The unit-ray form keeps the one-site purity deficits exactly as in the source. -/
theorem zeroReserveTransition_defect_le_unit [DecidableEq R] (u v : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) ≤
      Real.sqrt ((1 - frobSq (ptraceR (ketBra u u))) *
        (1 - frobSq (ptraceR (ketBra v v)))) := by
  simpa only [hu, hv, one_pow] using zeroReserveTransition_defect_le u v

private theorem zeroReserveTransition_hsInner_self {m n : Type*}
    [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    (hsInner X X).re = frobSq X := by
  rw [hsInner_re]
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, frobSq]

/-- The transition norm is the complementary reduced-state Hilbert--Schmidt pairing. -/
theorem zeroReserveTransition_frobSq_eq_pairing (u v : L × R → ℂ) :
    frobSq (ptraceL (ketBra u v)) =
      (hsInner (ptraceR (ketBra u u)) (ptraceR (ketBra v v))).re := by
  rw [← zeroReserveTransition_hsInner_self, hsInner_ptraceL_ketBra_cross,
    hsInner_re_comm]

/-- No normalization factor appears when tracing the reduced transition. -/
theorem zeroReserveTransition_trace (u v : L × R → ℂ) :
    (ptraceL (ketBra u v)).trace = braket v u := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceL, ketBra, braket,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- Orthogonality is exactly the trace-zero condition needed by the sharp trace inequality. -/
theorem zeroReserveTransition_trace_zero (u v : L × R → ℂ)
    (huv : braket u v = 0) : (ptraceL (ketBra u v)).trace = 0 := by
  rw [zeroReserveTransition_trace, ← conj_braket, huv, map_zero]

end Bipartite

section ThreeSites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

private theorem zeroReserveTransition_site2_right (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceR (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := by
  ext j k
  simp only [ptraceR, ptrace₁₃, Matrix.submatrix_apply, siteEquiv₂,
    Equiv.coe_fn_mk, Fintype.sum_prod_type]

private theorem zeroReserveTransition_site3_right (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceR (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := by
  ext j k
  simp only [ptraceR, ptrace₁₂, Matrix.submatrix_apply, siteEquiv₃,
    Equiv.coe_fn_mk, Fintype.sum_prod_type]

/-- The transition over site 1 is the actual `ptrace₁`, with purity of the retained site 1 state. -/
theorem zeroReserveTransition_site1 [DecidableEq b] [DecidableEq c]
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    nuclearTrace (ptrace₁ (ketBra u v)) ^ 2 - frobSq (ptrace₁ (ketBra u v)) ≤
      Real.sqrt ((1 - frobSq (ptrace₂₃ (ketBra u u))) *
        (1 - frobSq (ptrace₂₃ (ketBra v v)))) := by
  have hleft (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceL C = ptrace₁ C := rfl
  have hright (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR C = ptrace₂₃ C := by
    ext i j
    simp only [ptraceR, ptrace₂₃, Fintype.sum_prod_type]
  have h := zeroReserveTransition_defect_le_unit u v hu hv
  simpa only [hleft, hright] using h

/-- The same estimate at site 2, with literal manuscript contractions. -/
theorem zeroReserveTransition_site2 [DecidableEq a] [DecidableEq c]
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    nuclearTrace (ptrace₂ (ketBra u v)) ^ 2 - frobSq (ptrace₂ (ketBra u v)) ≤
      Real.sqrt ((1 - frobSq (ptrace₁₃ (ketBra u u))) *
        (1 - frobSq (ptrace₁₃ (ketBra v v)))) := by
  have h := zeroReserveTransition_defect_le_unit (u ∘ siteEquiv₂) (v ∘ siteEquiv₂)
    ((vecNormSq_comp_equiv siteEquiv₂ u).trans hu)
    ((vecNormSq_comp_equiv siteEquiv₂ v).trans hv)
  change nuclearTrace (ptrace₂ (ketBra u v)) ^ 2 - frobSq (ptrace₂ (ketBra u v)) ≤
    Real.sqrt ((1 - frobSq (ptraceR ((ketBra u u).submatrix siteEquiv₂ siteEquiv₂))) *
      (1 - frobSq (ptraceR ((ketBra v v).submatrix siteEquiv₂ siteEquiv₂)))) at h
  simpa only [zeroReserveTransition_site2_right] using h

/-- The same estimate at site 3, with literal manuscript contractions. -/
theorem zeroReserveTransition_site3 [DecidableEq a] [DecidableEq b]
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    nuclearTrace (ptrace₃ (ketBra u v)) ^ 2 - frobSq (ptrace₃ (ketBra u v)) ≤
      Real.sqrt ((1 - frobSq (ptrace₁₂ (ketBra u u))) *
        (1 - frobSq (ptrace₁₂ (ketBra v v)))) := by
  have h := zeroReserveTransition_defect_le_unit (u ∘ siteEquiv₃) (v ∘ siteEquiv₃)
    ((vecNormSq_comp_equiv siteEquiv₃ u).trans hu)
    ((vecNormSq_comp_equiv siteEquiv₃ v).trans hv)
  change nuclearTrace (ptrace₃ (ketBra u v)) ^ 2 - frobSq (ptrace₃ (ketBra u v)) ≤
    Real.sqrt ((1 - frobSq (ptraceR ((ketBra u u).submatrix siteEquiv₃ siteEquiv₃))) *
      (1 - frobSq (ptraceR ((ketBra v v).submatrix siteEquiv₃ siteEquiv₃)))) at h
  simpa only [zeroReserveTransition_site3_right] using h

/-- The first reduced transition loses no trace, hence orthogonal rays give trace zero. -/
theorem zeroReserveTransition_site1_trace_zero (u v : a × b × c → ℂ)
    (huv : braket u v = 0) : (ptrace₁ (ketBra u v)).trace = 0 :=
  zeroReserveTransition_trace_zero u v huv

theorem zeroReserveTransition_site2_trace_zero (u v : a × b × c → ℂ)
    (huv : braket u v = 0) : (ptrace₂ (ketBra u v)).trace = 0 := by
  exact zeroReserveTransition_trace_zero (u ∘ siteEquiv₂) (v ∘ siteEquiv₂)
    ((braket_comp_equiv siteEquiv₂ u v).trans huv)

theorem zeroReserveTransition_site3_trace_zero (u v : a × b × c → ℂ)
    (huv : braket u v = 0) : (ptrace₃ (ketBra u v)).trace = 0 := by
  exact zeroReserveTransition_trace_zero (u ∘ siteEquiv₃) (v ∘ siteEquiv₃)
    ((braket_comp_equiv siteEquiv₃ u v).trans huv)

/-- The two further contractions of a reduced transition are the literal double partial traces. -/
theorem zeroReserveTransition_site1_traces (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceL (ptrace₁ C) = ptrace₁₂ C ∧ ptraceR (ptrace₁ C) = ptrace₁₃ C := by
  constructor <;> ext i j
  · simp only [ptraceL, ptrace₁, ptrace₁₂]
    exact Finset.sum_comm
  · simp only [ptraceR, ptrace₁, ptrace₁₃]
    exact Finset.sum_comm

theorem zeroReserveTransition_site2_traces (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceL (ptrace₂ C) = ptrace₁₂ C ∧ ptraceR (ptrace₂ C) = ptrace₂₃ C := by
  constructor
  · rfl
  · ext i j
    simp only [ptraceR, ptrace₂, ptrace₂₃]
    exact Finset.sum_comm

theorem zeroReserveTransition_site3_traces (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceL (ptrace₃ C) = ptrace₁₃ C ∧ ptraceR (ptrace₃ C) = ptrace₂₃ C := by
  constructor <;> rfl

end ThreeSites

end ThreeCopyQutritWerner
