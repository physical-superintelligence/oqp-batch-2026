module

public import CGLMPBounds.Hardy.DeterminantTrace
public import CGLMPBounds.Hardy.Resolvent

@[expose] public section


/-!
# Resolvent traces equal the algebraic-multiplicity root fractions

This identifies the actual analytic trace integrand with the finite scalar root
sum. It is valid for arbitrary complex matrices, including defective ones.
Integrating around a separating contour and proving the cluster identities are
later steps; neither is assumed in the statements below.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_resolvent_eq (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) :
    Matrix.trace (A * resolvent A ζ) =
      ζ * Matrix.trace (resolvent A ζ) - (Fintype.card ι : ℂ) := by
  have hinv : (Matrix.scalar ι ζ - A) * resolvent A ζ = 1 := by
    rw [resolvent_eq_matrix_inverse]
    exact Matrix.mul_nonsing_inv _ (scalar_shift_det_isUnit A hζ)
  have hs : (Matrix.scalar ι ζ : Matrix ι ι ℂ) = ζ • 1 := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, h]
  have ht := congrArg Matrix.trace hinv
  rw [Matrix.sub_mul, hs, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one] at ht
  linear_combination -ht

/-- Weighted trace-resolvent identity with the full root multiset. -/
theorem trace_mul_resolvent_eq_root_sum (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) :
    Matrix.trace (A * resolvent A ζ) =
      (A.charpoly.roots.map (fun a => a / (ζ - a))).sum := by
  rw [trace_mul_resolvent_eq A hζ, trace_resolvent_eq_root_sum A hζ,
    weighted_root_fraction_sum A.charpoly.roots ζ
      (charpoly_root_ne_of_not_mem_spectrum A hζ), charpoly_roots_card]

/-- The previously constructed analytic pencil trace integrand is exactly the
source root-fraction sum divided by the matrix dimension. -/
theorem pencilTraceIntegrand_eq_root_sum (H Y : Matrix ι ι ℂ) {ζ z : ℂ}
    (hζ : ζ ∉ spectrum ℂ (traceDensityPencil H Y z)) :
    pencilTraceIntegrand H Y ζ z =
      (((traceDensityPencil H Y z).charpoly.roots).map
        (fun a => a / (ζ - a))).sum / (Fintype.card ι : ℂ) := by
  unfold pencilTraceIntegrand pencilResolvent
  rw [trace_mul_resolvent_eq_root_sum _ hζ]

end
end CGLMPBounds.Hardy
