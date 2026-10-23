module

public import VacuumBellSeparation.Gaussian.CrossRankOneSeries
public import VacuumBellSeparation.Gaussian.ComplexificationDenseExt

@[expose] public section


/-!
# Actual cross-rank-one matrix elements on real test vectors
-/

namespace VacuumBellSeparation.Gaussian

open HilbertComplexification
open scoped ComplexConjugate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

@[simp] theorem inner_complexification_ofReal (x y : E) :
    inner ℂ (ofReal x) (ofReal y) = (inner ℝ x y : ℂ) := by
  apply Complex.ext <;> simp [HilbertComplexification.inner_eq]

theorem inner_crossRankOne_real_moments
    (u : HilbertComplexification E) (v : HilbertComplexification F)
    (x y : E) (x' y' : F) (lx ly rx ry : ℝ)
    (hx : inner ℂ (ofReal x) u = (lx : ℂ))
    (hy : inner ℂ (ofReal y) u = (ly : ℂ))
    (hx' : inner ℂ (ofReal x') v = (rx : ℂ))
    (hy' : inner ℂ (ofReal y') v = (ry : ℂ)) :
    inner ℂ (WithLp.toLp 2 (ofReal x, ofReal x'))
      (crossRankOne u v (WithLp.toLp 2 (ofReal y, ofReal y'))) =
        ((lx * ry + rx * ly : ℝ) : ℂ) := by
  have huv : inner ℂ u (ofReal y) = (ly : ℂ) := by
    rw [← inner_conj_symm, hy]
    simp
  have hvv : inner ℂ v (ofReal y') = (ry : ℂ) := by
    rw [← inner_conj_symm, hy']
    simp
  rw [crossRankOne_apply, WithLp.prod_inner_apply]
  change inner ℂ (ofReal x) (inner ℂ v (ofReal y') • u) +
    inner ℂ (ofReal x') (inner ℂ u (ofReal y) • v) = _
  rw [inner_smul_right, inner_smul_right, hx, hx', huv, hvv]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  ring

end VacuumBellSeparation.Gaussian
