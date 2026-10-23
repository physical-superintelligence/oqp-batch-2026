module

public import CGLMPBounds.Partition.ArcFactorIntegrals

@[expose] public section


/-! Identification of the actual fractional-part arc count with its product
generating function under the literal uniform product measure. The origin-zero
case is proved directly; no rotation-preservation hypothesis is assumed. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem ae_boundaryPoints_mem_Ico (d : ℕ) :
    ∀ᵐ T : Fin d → ℝ ∂boundaryProductMeasure d,
      ∀ j : Fin d, T j ∈ Set.Ico (0 : ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro j
  exact (Measure.quasiMeasurePreserving_eval
    (μ := fun _ : Fin d => boundaryUniformMeasure) j).ae
      (ae_restrict_mem measurableSet_Ico)

theorem boundaryArcCount_pow_eq_prod (d : ℕ) (origin x : ℝ) (z : ℂ) (T : Fin d → ℝ) :
    z ^ boundaryArcCount d origin x T =
      ∏ j : Fin d, if Int.fract (T j - origin) < x then z else 1 := by
  classical
  unfold boundaryArcCount
  rw [← Finset.prod_filter]
  simp

theorem boundaryArcCount_zero_pow_ae_prod (d : ℕ) (x : ℝ) (z : ℂ) :
    (fun T : Fin d → ℝ => z ^ boundaryArcCount d 0 x T) =ᵐ[boundaryProductMeasure d]
      (fun T => ∏ j : Fin d, if T j < x then z else 1) := by
  filter_upwards [ae_boundaryPoints_mem_Ico d] with T hT
  rw [boundaryArcCount_pow_eq_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [sub_zero, Int.fract_eq_self.mpr (hT j)]

lemma integrable_arcFactor (x : ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => if t < x then z else 1) boundaryUniformMeasure := by
  classical
  have h : Integrable (fun t : ℝ =>
      (1 : ℂ) + (Set.Iio x).indicator (fun _ => z - 1) t) boundaryUniformMeasure :=
    (integrable_const (1 : ℂ)).add
      ((integrable_const (z - 1)).indicator measurableSet_Iio)
  apply h.congr
  filter_upwards [] with t
  by_cases ht : t < x <;> simp [ht, Set.mem_Iio]

theorem integrable_boundaryArcCount_zero_pow (d : ℕ) (x : ℝ) (z : ℂ) :
    Integrable (fun T : Fin d → ℝ => z ^ boundaryArcCount d 0 x T)
      (boundaryProductMeasure d) := by
  have hprod : Integrable (fun T : Fin d → ℝ =>
      ∏ j : Fin d, if T j < x then z else 1) (boundaryProductMeasure d) :=
    Integrable.fintype_prod (fun _ : Fin d => integrable_arcFactor x z)
  exact hprod.congr (boundaryArcCount_zero_pow_ae_prod d x z).symm

/-- The actual count has the binomial generating polynomial at origin zero.
This is an equality of actual integrals, not an assumed probability mass law. -/
theorem integral_boundaryArcCount_zero_pow (d : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T : Fin d → ℝ, z ^ boundaryArcCount d 0 x T ∂boundaryProductMeasure d) =
      (1 - (x : ℂ) + (x : ℂ) * z) ^ d := by
  rw [integral_congr_ae (boundaryArcCount_zero_pow_ae_prod d x z)]
  exact integral_prod_arcFactor d x hx z

end
end CGLMPBounds.Partition
