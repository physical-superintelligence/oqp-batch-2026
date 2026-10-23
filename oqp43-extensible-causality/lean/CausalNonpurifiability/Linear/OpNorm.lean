module

public import CausalNonpurifiability.Linear.OpNormDefinition
public import Mathlib
public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.OpNorm`

The operator (spectral) norm of a complex matrix, `opNorm H = ‖toEuclideanCLM H‖`
(Mathlib's `Matrix.toEuclideanCLM`, the star-algebra equivalence with bounded operators on
`EuclideanSpace ℂ ι`; the norm on the right is the operator norm), and the equivalence, for
Hermitian `H` and `r ≥ 0`, between the norm bound `‖H‖ ≤ r` and the two PSD bounds
`r • 1 ± H ≥ 0`.  The manuscript's ball hypothesis is the norm bound; the `InBall`
predicate uses the PSD bounds.

Route: PSD ⇔ nonnegative quadratic form `⟪v, M v⟫` on `EuclideanSpace` (`posSemidef_iff_inner_nonneg`);
`‖H‖ ≤ r ⇒` PSD bounds by Cauchy–Schwarz; PSD bounds `⇒ ‖H‖ ≤ r` through the orthonormal
eigenbasis `Matrix.IsHermitian.eigenvectorBasis` (`|λᵢ| ≤ r` from the quadratic form at
eigenvectors, then `‖H v‖² = ∑ λᵢ² |⟪eᵢ, v⟫|² ≤ r² ‖v‖²`).

Manuscript anchors: `thm:main` (iii) relative operator-norm ball, `eq:ball`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

namespace CausalNonpurifiability

variable {ι : Type}

theorem opNorm_nonneg [Fintype ι] [DecidableEq ι] (H : Op ι) : 0 ≤ opNorm H := norm_nonneg _

theorem opNorm_zero [Fintype ι] [DecidableEq ι] : opNorm (0 : Op ι) = 0 := by
  simp [opNorm]

/-! ### The induced operator and its quadratic form -/

/-- The quadratic form of a Hermitian matrix is real. -/
theorem im_star_dotProduct_mulVec [Fintype ι] {M : Op ι} (hM : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
  have h : star x ⬝ᵥ (M *ᵥ x) = star (star x ⬝ᵥ (M *ᵥ x)) := by
    conv_lhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, hM.eq, ← Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h.symm

/-- `⟪v, v⟫ = ‖v‖²` with a plain real-to-complex cast (in coordinates). -/
theorem inner_self_eq_ofReal_norm_sq [Fintype ι] (v : EuclideanSpace ℂ ι) :
    inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]

theorem real_mul_inner_self_cast [Fintype ι] (r : ℝ) (v : EuclideanSpace ℂ ι) :
    (r : ℂ) * inner ℂ v v = ((r * ‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_ofReal_norm_sq]
  push_cast
  ring

section Quadratic

variable [Fintype ι] [DecidableEq ι]

/-- `toEuclideanCLM H` acts by `H *ᵥ ·` in coordinates. -/
theorem toEuclideanCLM_apply_toLp (H : Op ι) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) H v = WithLp.toLp 2 (H *ᵥ v.ofLp) := by
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) v = _
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  exact Matrix.toLpLin_apply 2 2 H v

/-- `⟪v, H v⟫ = v* H v`: the quadratic form in coordinates. -/
theorem inner_toEuclideanCLM (H : Op ι) (v : EuclideanSpace ℂ ι) :
    inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v) = star v.ofLp ⬝ᵥ (H *ᵥ v.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, toEuclideanCLM_apply_toLp, WithLp.ofLp_toLp,
    dotProduct_comm]

/-- PSD ⇔ Hermitian with nonnegative quadratic form on `EuclideanSpace ℂ ι`. -/
theorem posSemidef_iff_inner_nonneg (M : Op ι) :
    M.PosSemidef ↔ M.IsHermitian ∧
      ∀ v : EuclideanSpace ℂ ι, 0 ≤ inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) M v) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine and_congr_right fun _ => ⟨fun h v => ?_, fun h x => ?_⟩
  · rw [inner_toEuclideanCLM]
    exact h _
  · have hx := h (WithLp.toLp 2 x)
    rwa [inner_toEuclideanCLM, WithLp.ofLp_toLp] at hx

theorem im_inner_toEuclideanCLM {H : Op ι} (hH : H.IsHermitian) (v : EuclideanSpace ℂ ι) :
    (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).im = 0 := by
  rw [inner_toEuclideanCLM]
  exact im_star_dotProduct_mulVec hH _

/-- `toEuclideanCLM H` is self-adjoint for Hermitian `H`. -/
theorem isSelfAdjoint_toEuclideanCLM {H : Op ι} (hH : H.IsHermitian) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) H) := by
  show star _ = _
  rw [← map_star, Matrix.star_eq_conjTranspose, hH.eq]

/-- Quadratic form of `r • 1 + H`. -/
theorem inner_toEuclideanCLM_smul_one_add (H : Op ι) (r : ℝ) (v : EuclideanSpace ℂ ι) :
    inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) ((r : ℂ) • (1 : Op ι) + H) v)
      = (r : ℂ) * inner ℂ v v + inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v) := by
  rw [map_add, map_smul, map_one, _root_.add_apply, _root_.smul_apply, one_apply_eq_self,
    inner_add_right, inner_smul_right]

/-- Quadratic form of `r • 1 - H`. -/
theorem inner_toEuclideanCLM_smul_one_sub (H : Op ι) (r : ℝ) (v : EuclideanSpace ℂ ι) :
    inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) ((r : ℂ) • (1 : Op ι) - H) v)
      = (r : ℂ) * inner ℂ v v - inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v) := by
  rw [map_sub, map_smul, map_one, _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right]

end Quadratic

theorem isHermitian_real_smul_one [DecidableEq ι] (r : ℝ) : ((r : ℂ) • (1 : Op ι)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

/-! ### Norm bound ⇔ PSD bounds -/

section Main

variable [Fintype ι] [DecidableEq ι]

/-- **Norm bound ⇔ PSD bounds** for Hermitian `H` and `r ≥ 0`:
`‖H‖ ≤ r ↔ r•1 + H ≥ 0 ∧ r•1 − H ≥ 0`. -/
theorem opNorm_le_iff_psd_bounds {H : Op ι} (hH : H.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    opNorm H ≤ r ↔
      ((r : ℂ) • (1 : Op ι) + H).PosSemidef ∧ ((r : ℂ) • (1 : Op ι) - H).PosSemidef := by
  unfold opNorm
  have him : ∀ v : EuclideanSpace ℂ ι,
      (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).im = 0 :=
    fun v => im_inner_toEuclideanCLM hH v
  constructor
  · -- norm bound ⇒ quadratic form bounds ⇒ PSD bounds
    intro hnorm
    have bound : ∀ v : EuclideanSpace ℂ ι,
        |(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re| ≤ r * ‖v‖ ^ 2 := by
      intro v
      calc |(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re|
          ≤ ‖inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H v‖ := norm_inner_le_norm _ _
        _ ≤ ‖v‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) H‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℂ) H).le_opNorm v)
              (norm_nonneg v)
        _ ≤ ‖v‖ * (r * ‖v‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
              (norm_nonneg v)
        _ = r * ‖v‖ ^ 2 := by ring
    refine ⟨(posSemidef_iff_inner_nonneg _).mpr
        ⟨(isHermitian_real_smul_one r).add hH, fun v => ?_⟩,
      (posSemidef_iff_inner_nonneg _).mpr
        ⟨(isHermitian_real_smul_one r).sub hH, fun v => ?_⟩⟩
    · rw [inner_toEuclideanCLM_smul_one_add, real_mul_inner_self_cast, Complex.nonneg_iff,
        Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, him v]
      exact ⟨by linarith [(abs_le.mp (bound v)).1], by simp⟩
    · rw [inner_toEuclideanCLM_smul_one_sub, real_mul_inner_self_cast, Complex.nonneg_iff,
        Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, him v]
      exact ⟨by linarith [(abs_le.mp (bound v)).2], by simp⟩
  · -- PSD bounds ⇒ eigenvalue bounds ⇒ norm bound
    rintro ⟨hplus, hminus⟩
    have hq : ∀ v : EuclideanSpace ℂ ι,
        |(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re| ≤ r * ‖v‖ ^ 2 := by
      intro v
      have h1 := ((posSemidef_iff_inner_nonneg _).mp hplus).2 v
      have h2 := ((posSemidef_iff_inner_nonneg _).mp hminus).2 v
      rw [inner_toEuclideanCLM_smul_one_add, real_mul_inner_self_cast, Complex.nonneg_iff,
        Complex.add_re, Complex.ofReal_re] at h1
      rw [inner_toEuclideanCLM_smul_one_sub, real_mul_inner_self_cast, Complex.nonneg_iff,
        Complex.sub_re, Complex.ofReal_re] at h2
      exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h2.1]⟩
    have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_toEuclideanCLM hH)
    have hsym : ∀ x y : EuclideanSpace ℂ ι,
        inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) H x) y
          = inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) H y) := fun x y => hsymm x y
    -- eigenvectors
    have hTb : ∀ i, Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis i)
        = ((hH.eigenvalues i : ℝ) : ℂ) • hH.eigenvectorBasis i := by
      intro i
      rw [toEuclideanCLM_apply_toLp, hH.mulVec_eigenvectorBasis, WithLp.toLp_smul,
        WithLp.toLp_ofLp, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    have hlam : ∀ i, |hH.eigenvalues i| ≤ r := by
      intro i
      have h := hq (hH.eigenvectorBasis i)
      rw [hTb i, inner_smul_right, inner_self_eq_ofReal_norm_sq,
        hH.eigenvectorBasis.orthonormal.1 i] at h
      simpa using h
    refine ContinuousLinearMap.opNorm_le_bound _ hr fun v => ?_
    have hrepr : ∀ i, (hH.eigenvectorBasis.repr (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).ofLp i
        = ((hH.eigenvalues i : ℝ) : ℂ) * (hH.eigenvectorBasis.repr v).ofLp i := by
      intro i
      rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hsym, hTb i,
        inner_smul_left, Complex.conj_ofReal]
    have key : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H v‖ ^ 2 ≤ (r * ‖v‖) ^ 2 := by
      rw [← hH.eigenvectorBasis.repr.norm_map (Matrix.toEuclideanCLM (𝕜 := ℂ) H v),
        ← hH.eigenvectorBasis.repr.norm_map v, mul_pow, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hrepr i, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hlam i) 2)
        (sq_nonneg _)
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H v‖
        = Real.sqrt (‖Matrix.toEuclideanCLM (𝕜 := ℂ) H v‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((r * ‖v‖) ^ 2) := Real.sqrt_le_sqrt key
      _ = r * ‖v‖ := Real.sqrt_sq (mul_nonneg hr (norm_nonneg _))

/-- The direction consumed by the ball theorem: a norm bound gives the PSD bounds. -/
theorem psd_bounds_of_opNorm_le {H : Op ι} (hH : H.IsHermitian) {r : ℝ} (hr : 0 ≤ r)
    (h : opNorm H ≤ r) :
    ((r : ℂ) • (1 : Op ι) + H).PosSemidef ∧ ((r : ℂ) • (1 : Op ι) - H).PosSemidef :=
  (opNorm_le_iff_psd_bounds hH hr).mp h

end Main

end CausalNonpurifiability
