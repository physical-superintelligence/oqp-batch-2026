module

public import ThreeCopyQutritWerner.CertificateDescendantGram
public import ThreeCopyQutritWerner.CertificatePhysicalRealization
public import ThreeCopyQutritWerner.CertificateBlockTransport
public import Mathlib.Analysis.Matrix.Order

@[expose] public section


/-!
# Positivity in the exact repeated source metric

The Schur product theorem applies to the scalar descendant metric and the
original source blocks. The scalar metric itself is recovered from a physical
principal Gram matrix by a positive type-dependent rescaling. No Euclidean
replacement of the original source Gram is made.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The repeated metric is an actual Hadamard product of two physical pullbacks. -/
theorem certificateRepeatedFrameMetric_eq_hadamard
    {F T : Type*} [DecidableEq T] (size : T → ℕ) (type : F → T)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) :
    certificateRepeatedFrameMetric size type G K =
      K.submatrix Sigma.fst Sigma.fst ⊙
        (Matrix.blockDiagonal' G).submatrix
          (fun i : Σ f, Fin (size (type f)) => ⟨type i.1, i.2⟩)
          (fun i : Σ f, Fin (size (type f)) => ⟨type i.1, i.2⟩) := by
  have hcast (t u : T) (h : t = u) (j : Fin (size u)) :
      (h.symm ▸ j) = cast (congrArg (fun v => Fin (size v)) h.symm) j := by
    cases h
    rfl
  ext i j
  by_cases h : type i.1 = type j.1 <;>
    simp [certificateRepeatedFrameMetric, Matrix.hadamard_apply,
      Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h, hcast]

/-- Positive scalar and original source metrics give a positive repeated metric. -/
theorem certificateRepeatedFrameMetric_posSemidef
    {F T : Type*} [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) (hK : K.PosSemidef) (hG : ∀ t, (G t).PosSemidef) :
    (certificateRepeatedFrameMetric size type G K).PosSemidef := by
  rw [certificateRepeatedFrameMetric_eq_hadamard]
  exact (hK.submatrix Sigma.fst).hadamard
    ((certificate_blockDiagonal_posSemidef G hG).submatrix _)

private theorem certificate_repeated_metric_sum
    {T : Type*} (size : T → ℕ)
    (G A : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (t u : T) (h : t = u) (z : ℂ) (i : Fin (size t)) (j : Fin (size u)) :
    (∑ k : Fin (size u), (z * G t i (h.symm ▸ k)) * A u k j) =
      z * (G t * A t) i (h.symm ▸ j) := by
  subst u
  simp only [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- The true full Gram times a repeated action keeps the same scalar frame metric. -/
theorem certificateRepeatedFrameMetric_mul
    {F T : Type*} [Fintype F] [DecidableEq F] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (G A : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) :
    certificateRepeatedFrameMetric size type G K *
        Matrix.blockDiagonal' (fun f => A (type f)) =
      certificateRepeatedFrameMetric size type (fun t => G t * A t) K := by
  ext ⟨f, i⟩ ⟨g, j⟩
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single g]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    by_cases h : type f = type g
    · simp only [certificateRepeatedFrameMetric, dif_pos h]
      exact certificate_repeated_metric_sum size G A (type f) (type g) h (K f g) i j
    · simp only [certificateRepeatedFrameMetric, dif_neg h, zero_mul,
        Finset.sum_const_zero]
  · intro g' hg'
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hg', mul_zero]

/-- An exact physical Gram factorization turns positive source blocks into a
positive full-metric quadratic form, with all descendant overlaps retained. -/
theorem certificateRepeatedFrameMetric_action_posSemidef
    {F T : Type*} [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (G A : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) (hK : K.PosSemidef)
    (hGA : ∀ t, (G t * A t).PosSemidef) :
    (certificateRepeatedFrameMetric size type G K *
      Matrix.blockDiagonal' (fun f => A (type f))).PosSemidef := by
  rw [certificateRepeatedFrameMetric_mul]
  exact certificateRepeatedFrameMetric_posSemidef size type _ K hK hGA

/-- Recover the scalar frame metric from a principal physical Gram, using
only the positive diagonal of each unchanged original source metric. -/
theorem certificate_scalar_metric_posSemidef
    {F T : Type*} [DecidableEq T] (type : F → T)
    (K H : Matrix F F ℂ) (g : T → ℝ) (hg : ∀ t, 0 < g t)
    (hH : H.PosSemidef)
    (hzero : ∀ f f', type f ≠ type f' → K f f' = 0)
    (hentry : ∀ f f', H f f' =
      if type f = type f' then K f f' * (g (type f) : ℂ) else 0) :
    K.PosSemidef := by
  let D : Matrix T T ℂ := Matrix.diagonal (fun t => ((g t)⁻¹ : ℝ))
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro t
    change (0 : ℂ) ≤ ((g t)⁻¹ : ℝ)
    exact_mod_cast inv_nonneg.mpr (hg t).le
  have heq : H ⊙ D.submatrix type type = K := by
    ext f f'
    by_cases h : type f = type f'
    · have hn : (g (type f') : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hg (type f')))
      simp [Matrix.hadamard_apply, Matrix.submatrix_apply, D, Matrix.diagonal_apply,
        hentry, h, Complex.ofReal_inv, mul_assoc, hn]
    · simp [Matrix.hadamard_apply, Matrix.submatrix_apply, D, Matrix.diagonal_apply,
        hentry, h, hzero f f' h]
  rw [← heq]
  exact hH.hadamard (hD.submatrix type)

/-- Positive original source blocks yield an actual positive physical operator,
once the checked complete basis and its literal repeated Gram are supplied. -/
theorem certificate_repeated_realization_posSemidef
    {n F T : Type*} [Fintype n] [DecidableEq n]
    [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (S : Matrix n (Σ f, Fin (size (type f))) ℂ)
    (V : Matrix (Σ f, Fin (size (type f))) n ℂ)
    (G A : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) (hSV : S * V = 1)
    (hGram : Sᴴ * S = certificateRepeatedFrameMetric size type G K)
    (hK : K.PosSemidef) (hGA : ∀ t, (G t * A t).PosSemidef) :
    (S * Matrix.blockDiagonal' (fun f => A (type f)) * V).PosSemidef := by
  apply certificate_realization_posSemidef S V _ hSV
  rw [hGram]
  exact certificateRepeatedFrameMetric_action_posSemidef size type G A K hK hGA

end ThreeCopyQutritWerner
