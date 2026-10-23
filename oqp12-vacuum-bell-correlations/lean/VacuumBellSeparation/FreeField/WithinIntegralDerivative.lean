module

public import Mathlib

@[expose] public section


/-!
# A genuine dominated derivative of a scalar integral within a set

This is the closed-half-plane variant needed by the positive-energy
Laplace argument. It follows directly from actual integrability, the
complex difference-quotient characterization and dominated convergence.
-/

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped Topology

theorem hasDerivWithinAt_integral_of_dominated_slope
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℂ → α → ℂ) (D : α → ℂ) (s : Set ℂ) (z₀ : ℂ) (hz₀ : z₀ ∈ s)
    (hF : ∀ z ∈ s, Integrable (F z) μ)
    (hD : ∀ a, HasDerivWithinAt (fun z => F z a) (D a) s z₀)
    (B : α → ℝ) (hB : Integrable B μ)
    (hbound : ∀ z ∈ s, ∀ a, ‖F z a - F z₀ a‖ ≤ B a * ‖z - z₀‖) :
    HasDerivWithinAt (fun z => ∫ a, F z a ∂μ) (∫ a, D a ∂μ) s z₀ := by
  have hs : ∀ᶠ z in 𝓝[s \ {z₀}] z₀, z ∈ s \ {z₀} := self_mem_nhdsWithin
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[s \ {z₀}] z₀) (F := fun z a => slope (fun w => F w a) z₀ z)
    (f := D) B
    (hs.mono fun z hz => by
      simp only [slope_def_field]
      exact ((hF z hz.1).sub (hF z₀ hz₀)).div_const (z - z₀) |>.aestronglyMeasurable)
    (hs.mono fun z hz => Eventually.of_forall fun a => by
      have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
      rw [slope_def_field, norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr hne)).mpr (hbound z hz.1 a))
    hB (Eventually.of_forall fun a => hasDerivWithinAt_iff_tendsto_slope.mp (hD a))
  rw [hasDerivWithinAt_iff_tendsto_slope]
  apply (tendsto_congr' (hs.mono fun z hz => ?_)).mp ht
  simp only [slope_def_field]
  rw [integral_div, integral_sub (hF z hz.1) (hF z₀ hz₀)]

end VacuumBellSeparation
