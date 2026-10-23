module

public import VacuumBellSeparation.FreeField.EvolutionGenerator

@[expose] public section


/-!
# Actual bounded multiplication on spatial L²

The multiplier is constructed by the existing Hölder bilinear map with
exponents infinity, two and two. Lebesgue space is not assumed to have finite
measure. The operation agrees with actual Schwartz multiplication whenever
the coefficient has temperate growth.
-/

namespace VacuumBellSeparation

open MeasureTheory

noncomputable abbrev SpatialL2 := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

noncomputable def boundedL2Multiplier (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : MemLp w ⊤ volume) : SpatialL2 →L[ℂ] SpatialL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (hw.toLp w)

theorem coeFn_boundedL2Multiplier (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : MemLp w ⊤ volume) (f : SpatialL2) :
    (boundedL2Multiplier w hw f : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
      fun x => w x * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hw.toLp w) f
  filter_upwards [h, hw.coeFn_toLp] with x hx hxw
  change boundedL2Multiplier w hw f x = _
  simpa only [boundedL2Multiplier, ContinuousLinearMap.holderL_apply_apply,
    hxw, ContinuousLinearMap.mul_apply'] using hx

theorem norm_boundedL2Multiplier_apply_le (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : MemLp w ⊤ volume) {C : ℝ} (hC : ∀ᵐ x, ‖w x‖ ≤ C) (f : SpatialL2) :
    ‖boundedL2Multiplier w hw f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_boundedL2Multiplier w hw f, hC] with x hx hcx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hcx (norm_nonneg _)

theorem norm_boundedL2Multiplier_le (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : MemLp w ⊤ volume) {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ᵐ x, ‖w x‖ ≤ C) :
    ‖boundedL2Multiplier w hw‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC₀ (norm_boundedL2Multiplier_apply_le w hw hC)

theorem boundedL2Multiplier_toLp (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : MemLp w ⊤ volume) (ht : Function.HasTemperateGrowth w) (f : SpatialSchwartz) :
    boundedL2Multiplier w hw (f.toLp 2) = (SchwartzMap.smulLeftCLM ℂ w f).toLp 2 := by
  apply Lp.ext
  filter_upwards [coeFn_boundedL2Multiplier w hw (f.toLp 2), f.coeFn_toLp 2,
    (SchwartzMap.smulLeftCLM ℂ w f).coeFn_toLp 2] with x hx hfx hprod
  rw [hx, hfx, hprod, SchwartzMap.smulLeftCLM_apply_apply ht]
  rfl

end VacuumBellSeparation
