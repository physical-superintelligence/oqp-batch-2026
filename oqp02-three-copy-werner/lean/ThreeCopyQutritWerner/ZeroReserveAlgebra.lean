module

public import ThreeCopyQutritWerner.ZeroReserveTransition

@[expose] public section


/-!
# Exact two-ray expansion of the manuscript reserve

The reserve is the literal contraction form `(3N−2A+B)/4`, equivalently
`q−(2N−T)/8`. Its expansion on a real linear combination of two orthonormal
ray projections is proved from finite Hilbert--Schmidt polarization and the
complementary partial-trace cross identity. No reserve sign, sharp nuclear
partial-trace estimate, or equality classification is assumed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section ScalarPolarization

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Literal complex sesquilinearity of the finite matrix inner product. -/
theorem zeroReserve_hsInner_smul (A B : Matrix m n ℂ) (z w : ℂ) :
    hsInner (z • A) (w • B) = conj z * w * hsInner A B := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Real scalar polarization, with no Hermiticity requirement on the two matrices. -/
theorem zeroReserve_frobSq_real_mix (A B : Matrix m n ℂ) (lam mu : ℝ) :
    frobSq ((lam : ℂ) • A + (mu : ℂ) • B) =
      lam ^ 2 * frobSq A + mu ^ 2 * frobSq B +
        2 * lam * mu * (hsInner A B).re := by
  rw [frobSq_add, frobSq_smul, frobSq_smul, zeroReserve_hsInner_smul]
  simp only [Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem zeroReserve_hsInner_self_re (A : Matrix m n ℂ) :
    (hsInner A A).re = frobSq A := by
  rw [hsInner_re]
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, frobSq]

end ScalarPolarization

section BipartitePairing

variable {L R : Type*} [Fintype L] [Fintype R]

/-- Complementary form of the reduced-transition norm identity. -/
theorem zeroReserveTransition_frobSq_right_eq_pairing (u v : L × R → ℂ) :
    frobSq (ptraceR (ketBra u v)) =
      (hsInner (ptraceL (ketBra u u)) (ptraceL (ketBra v v))).re := by
  rw [← zeroReserve_hsInner_self_re, hsInner_ptraceR_ketBra_cross,
    hsInner_re_comm]

end BipartitePairing

section ThreeSites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The exact manuscript reserve `r(C,C†)`, written in its real contraction form. -/
def zeroReserve (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (3 * invN C - 2 * invA C + invB C) / 4

/-- The sum of the three one-site linear entropy deficits for a unit ray. -/
def zeroReserveLocalEntropy (u : a × b × c → ℂ) : ℝ :=
  3 - invB (ketBra u u)

/-- The reserve retains the manuscript's exact endpoint normalization. -/
theorem zeroReserve_eq_endpoint (C : Matrix (a × b × c) (a × b × c) ℂ) :
    zeroReserve C = endpointEnergy C - (2 * invN C - invT C) / 8 := by
  unfold zeroReserve endpointEnergy energy
  ring

private def zeroReservePairA (A B : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (hsInner (ptrace₁ A) (ptrace₁ B)).re +
    (hsInner (ptrace₂ A) (ptrace₂ B)).re + (hsInner (ptrace₃ A) (ptrace₃ B)).re

private def zeroReservePairB (A B : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (hsInner (ptrace₁₂ A) (ptrace₁₂ B)).re +
    (hsInner (ptrace₁₃ A) (ptrace₁₃ B)).re + (hsInner (ptrace₂₃ A) (ptrace₂₃ B)).re

private theorem zeroReservePairA_ketBra (u v : a × b × c → ℂ) :
    zeroReservePairA (ketBra u u) (ketBra v v) = invB (ketBra u v) := by
  have hr1 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR C = ptrace₂₃ C := by
    ext i j
    simp only [ptraceR, ptrace₂₃, Fintype.sum_prod_type]
  have hr2 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := by
    ext i j
    simp only [ptraceR, ptrace₁₃, Matrix.submatrix_apply, siteEquiv₂,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have hr3 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := by
    ext i j
    simp only [ptraceR, ptrace₁₂, Matrix.submatrix_apply, siteEquiv₃,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have h1 := zeroReserveTransition_frobSq_right_eq_pairing u v
  have h2 := zeroReserveTransition_frobSq_right_eq_pairing
    (u ∘ siteEquiv₂) (v ∘ siteEquiv₂)
  have h3 := zeroReserveTransition_frobSq_right_eq_pairing
    (u ∘ siteEquiv₃) (v ∘ siteEquiv₃)
  have e1 : frobSq (ptrace₂₃ (ketBra u v)) =
      (hsInner (ptrace₁ (ketBra u u)) (ptrace₁ (ketBra v v))).re := by
    change frobSq (ptraceR (ketBra u v)) =
      (hsInner (ptrace₁ (ketBra u u)) (ptrace₁ (ketBra v v))).re at h1
    simpa only [hr1] using h1
  have e2 : frobSq (ptrace₁₃ (ketBra u v)) =
      (hsInner (ptrace₂ (ketBra u u)) (ptrace₂ (ketBra v v))).re := by
    change frobSq (ptraceR ((ketBra u v).submatrix siteEquiv₂ siteEquiv₂)) =
      (hsInner (ptrace₂ (ketBra u u)) (ptrace₂ (ketBra v v))).re at h2
    simpa only [hr2] using h2
  have e3 : frobSq (ptrace₁₂ (ketBra u v)) =
      (hsInner (ptrace₃ (ketBra u u)) (ptrace₃ (ketBra v v))).re := by
    change frobSq (ptraceR ((ketBra u v).submatrix siteEquiv₃ siteEquiv₃)) =
      (hsInner (ptrace₃ (ketBra u u)) (ptrace₃ (ketBra v v))).re at h3
    simpa only [hr3] using h3
  unfold zeroReservePairA invB
  rw [← e1, ← e2, ← e3]
  ring

private theorem zeroReservePairB_ketBra (u v : a × b × c → ℂ) :
    zeroReservePairB (ketBra u u) (ketBra v v) = invA (ketBra u v) := by
  have hr1 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR C = ptrace₂₃ C := by
    ext i j
    simp only [ptraceR, ptrace₂₃, Fintype.sum_prod_type]
  have hr2 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := by
    ext i j
    simp only [ptraceR, ptrace₁₃, Matrix.submatrix_apply, siteEquiv₂,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have hr3 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := by
    ext i j
    simp only [ptraceR, ptrace₁₂, Matrix.submatrix_apply, siteEquiv₃,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have h1 := zeroReserveTransition_frobSq_eq_pairing u v
  have h2 := zeroReserveTransition_frobSq_eq_pairing
    (u ∘ siteEquiv₂) (v ∘ siteEquiv₂)
  have h3 := zeroReserveTransition_frobSq_eq_pairing
    (u ∘ siteEquiv₃) (v ∘ siteEquiv₃)
  have e1 : frobSq (ptrace₁ (ketBra u v)) =
      (hsInner (ptrace₂₃ (ketBra u u)) (ptrace₂₃ (ketBra v v))).re := by
    change frobSq (ptrace₁ (ketBra u v)) =
      (hsInner (ptraceR (ketBra u u)) (ptraceR (ketBra v v))).re at h1
    simpa only [hr1] using h1
  have e2 : frobSq (ptrace₂ (ketBra u v)) =
      (hsInner (ptrace₁₃ (ketBra u u)) (ptrace₁₃ (ketBra v v))).re := by
    change frobSq (ptrace₂ (ketBra u v)) =
      (hsInner (ptraceR ((ketBra u u).submatrix siteEquiv₂ siteEquiv₂)) (ptraceR ((ketBra v v).submatrix siteEquiv₂ siteEquiv₂))).re at h2
    simpa only [hr2] using h2
  have e3 : frobSq (ptrace₃ (ketBra u v)) =
      (hsInner (ptrace₁₂ (ketBra u u)) (ptrace₁₂ (ketBra v v))).re := by
    change frobSq (ptrace₃ (ketBra u v)) =
      (hsInner (ptraceR ((ketBra u u).submatrix siteEquiv₃ siteEquiv₃)) (ptraceR ((ketBra v v).submatrix siteEquiv₃ siteEquiv₃))).re at h3
    simpa only [hr3] using h3
  unfold zeroReservePairB invA
  rw [← e1, ← e2, ← e3]
  ring

/-- A pure ray has equal total one-trace and two-trace purity. -/
theorem zeroReserve_invA_eq_invB_pure (u : a × b × c → ℂ) :
    invA (ketBra u u) = invB (ketBra u u) := by
  have h := zeroReservePairA_ketBra u u
  simpa only [zeroReservePairA, zeroReserve_hsInner_self_re, invA] using h

private theorem zeroReserve_ptrace₁_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁ (A + B) = ptrace₁ A + ptrace₁ B := by
  ext i j
  simp only [ptrace₁, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_ptrace₂_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂ (A + B) = ptrace₂ A + ptrace₂ B := by
  ext i j
  simp only [ptrace₂, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_ptrace₃_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₃ (A + B) = ptrace₃ A + ptrace₃ B := by
  ext i j
  simp only [ptrace₃, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_ptrace₁₂_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₂ (A + B) = ptrace₁₂ A + ptrace₁₂ B := by
  ext i j
  simp only [ptrace₁₂, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_ptrace₁₃_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₃ (A + B) = ptrace₁₃ A + ptrace₁₃ B := by
  ext i j
  simp only [ptrace₁₃, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_ptrace₂₃_add
    (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂₃ (A + B) = ptrace₂₃ A + ptrace₂₃ B := by
  ext i j
  simp only [ptrace₂₃, Matrix.add_apply, Finset.sum_add_distrib]

private theorem zeroReserve_invA_mix
    (A B : Matrix (a × b × c) (a × b × c) ℂ) (lam mu : ℝ) :
    invA ((lam : ℂ) • A + (mu : ℂ) • B) =
      lam ^ 2 * invA A + mu ^ 2 * invA B + 2 * lam * mu * zeroReservePairA A B := by
  simp only [invA, zeroReservePairA,
    zeroReserve_ptrace₁_add, zeroReserve_ptrace₂_add, zeroReserve_ptrace₃_add,
    ptrace₁_smul, ptrace₂_smul, ptrace₃_smul, zeroReserve_frobSq_real_mix]
  ring

private theorem zeroReserve_invB_mix
    (A B : Matrix (a × b × c) (a × b × c) ℂ) (lam mu : ℝ) :
    invB ((lam : ℂ) • A + (mu : ℂ) • B) =
      lam ^ 2 * invB A + mu ^ 2 * invB B + 2 * lam * mu * zeroReservePairB A B := by
  simp only [invB, zeroReservePairB,
    zeroReserve_ptrace₁₂_add, zeroReserve_ptrace₁₃_add, zeroReserve_ptrace₂₃_add,
    ptrace₁₂_smul, ptrace₁₃_smul, ptrace₂₃_smul, zeroReserve_frobSq_real_mix]
  ring

/-- Exact reserve quadratic for two orthonormal rays, with arbitrary real coefficients. -/
theorem zeroReserve_two_ray_expansion (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) :
    4 * zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) =
      lam ^ 2 * zeroReserveLocalEntropy u + mu ^ 2 * zeroReserveLocalEntropy v -
        2 * lam * mu * (2 * invB (ketBra u v) - invA (ketBra u v)) := by
  have hn : invN ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) =
      lam ^ 2 + mu ^ 2 := by
    simp only [invN, zeroReserve_frobSq_real_mix, frobSq_ketBra_vecNormSq,
      hsInner_ketBra, hu, hv, huv, map_zero, zero_mul, Complex.zero_re,
      mul_one, mul_zero, add_zero]
  unfold zeroReserve zeroReserveLocalEntropy
  rw [hn, zeroReserve_invA_mix, zeroReserve_invB_mix,
    zeroReservePairA_ketBra, zeroReservePairB_ketBra,
    zeroReserve_invA_eq_invB_pure, zeroReserve_invA_eq_invB_pure]
  ring

/-- For a unit ray the reserve is one quarter of its total one-site linear entropy. -/
theorem zeroReserve_pure (u : a × b × c → ℂ) (hu : vecNormSq u = 1) :
    4 * zeroReserve (ketBra u u) = zeroReserveLocalEntropy u := by
  unfold zeroReserve zeroReserveLocalEntropy invN
  rw [frobSq_ketBra_vecNormSq, hu, zeroReserve_invA_eq_invB_pure]
  ring

/-- The source entropy is exactly the sum of its three displayed local deficits. -/
theorem zeroReserveLocalEntropy_eq (u : a × b × c → ℂ) :
    zeroReserveLocalEntropy u =
      (1 - frobSq (ptrace₂₃ (ketBra u u))) +
      (1 - frobSq (ptrace₁₃ (ketBra u u))) +
      (1 - frobSq (ptrace₁₂ (ketBra u u))) := by
  unfold zeroReserveLocalEntropy invB
  ring

/-- All three local entropy deficits are nonnegative for a unit ray. -/
theorem zeroReserveLocalEntropy_deficits_nonneg (u : a × b × c → ℂ)
    (hu : vecNormSq u = 1) :
    0 ≤ 1 - frobSq (ptrace₂₃ (ketBra u u)) ∧
    0 ≤ 1 - frobSq (ptrace₁₃ (ketBra u u)) ∧
    0 ≤ 1 - frobSq (ptrace₁₂ (ketBra u u)) := by
  have hr1 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR C = ptrace₂₃ C := by
    ext i j
    simp only [ptraceR, ptrace₂₃, Fintype.sum_prod_type]
  have hr2 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := by
    ext i j
    simp only [ptraceR, ptrace₁₃, Matrix.submatrix_apply, siteEquiv₂,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have hr3 (C : Matrix (a × b × c) (a × b × c) ℂ) :
      ptraceR (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := by
    ext i j
    simp only [ptraceR, ptrace₁₂, Matrix.submatrix_apply, siteEquiv₃,
      Equiv.coe_fn_mk, Fintype.sum_prod_type]
  have h1 := zeroReserveTransition_purity_defect_nonneg u
  have h2 := zeroReserveTransition_purity_defect_nonneg (u ∘ siteEquiv₂)
  have h3 := zeroReserveTransition_purity_defect_nonneg (u ∘ siteEquiv₃)
  have hn2 : vecNormSq (u ∘ siteEquiv₂) = 1 :=
    (vecNormSq_comp_equiv siteEquiv₂ u).trans hu
  have hn3 : vecNormSq (u ∘ siteEquiv₃) = 1 :=
    (vecNormSq_comp_equiv siteEquiv₃ u).trans hu
  rw [hn2, one_pow] at h2
  rw [hn3, one_pow] at h3
  rw [hu, one_pow] at h1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr1] using h1
  · change 0 ≤ 1 - frobSq (ptraceR
      ((ketBra u u).submatrix siteEquiv₂ siteEquiv₂)) at h2
    simpa only [hr2] using h2
  · change 0 ≤ 1 - frobSq (ptraceR
      ((ketBra u u).submatrix siteEquiv₃ siteEquiv₃)) at h3
    simpa only [hr3] using h3

theorem zeroReserveLocalEntropy_nonneg (u : a × b × c → ℂ) (hu : vecNormSq u = 1) :
    0 ≤ zeroReserveLocalEntropy u := by
  rw [zeroReserveLocalEntropy_eq]
  obtain ⟨h1, h2, h3⟩ := zeroReserveLocalEntropy_deficits_nonneg u hu
  linarith

end ThreeSites

end ThreeCopyQutritWerner
