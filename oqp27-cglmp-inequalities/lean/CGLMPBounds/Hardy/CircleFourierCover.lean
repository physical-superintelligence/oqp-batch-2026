module

public import CGLMPBounds.Defs.CircularHilbert
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section


/-! Actual normalized circle covering and Fourier coefficient transport.
The fourth-power map preserves Haar measure; its coefficient support is
proved from the quarter-turn symmetry. -/

namespace CGLMPBounds.Hardy
open MeasureTheory MeasureTheory.Measure Matrix
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance {r : ℕ} : ContinuousENorm (Circulation.Mat r) :=
  inferInstanceAs (ContinuousENorm (Fin r → Fin r → ℂ))

 theorem circle_representative_measurePreserving :
    MeasurePreserving (fun t : UnitCircle => (AddCircle.equivIoc 1 0 t : ℝ))
      circleMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have h := (measurePreserving_subtype_coe (measurableSet_Ioc (a := (0 : ℝ)) (b := 0+1))).comp
    (AddCircle.measurePreserving_equivIoc 1 (a := 0))
  simpa only [Function.comp_def, zero_add, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] using h

theorem intervalCircleLift_integrable {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    Integrable (intervalCircleLift U) circleMeasure := by
  simpa only [intervalCircleLift, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def] using
    circle_representative_measurePreserving.integrable_comp_of_integrable hU

theorem circle_quadruple_measurePreserving :
    MeasurePreserving (fun t : UnitCircle => 4 • t) circleMeasure circleMeasure := by
  simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using!
    (measurePreserving_zsmul circleMeasure (by norm_num : (4 : ℤ) ≠ 0))

theorem circle_integral_quadruple {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : UnitCircle → E) (hf : AEStronglyMeasurable f circleMeasure) :
    (∫ t, f (4 • t) ∂circleMeasure) = ∫ t, f t ∂circleMeasure := by
  have hmap := circle_quadruple_measurePreserving.map_eq
  rw [← hmap] at hf
  have h := integral_map circle_quadruple_measurePreserving.measurable.aemeasurable hf
  simpa only [hmap] using h.symm

theorem circle_fourier_quadruple (k : ℤ) (t : UnitCircle) :
    fourier k (4 • t) = fourier (4*k) t := by
  simp only [fourier_apply]
  congr 1
  rw [← natCast_zsmul, smul_smul]
  congr 1
  ring

theorem circle_fourier_modulation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : UnitCircle → E) (m k : ℤ) :
    fourierCoeff (fun t => fourier m t • f t) k = fourierCoeff f (k-m) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_smul, ← fourier_add]
  congr 2
  ring

theorem circle_fourierCoeff_quadruple {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : UnitCircle → E) (hf : Integrable f circleMeasure) (k : ℤ) :
    fourierCoeff (fun t => f (4 • t)) (4*k) = fourierCoeff f k := by
  unfold fourierCoeff
  have hchar (t : UnitCircle) : fourier (-(4*k)) t = fourier (-k) (4 • t) := by
    rw [circle_fourier_quadruple]
    congr 1
    ring
  simp_rw [hchar]
  exact circle_integral_quadruple _ (hf.fourier_smul (-k)).aestronglyMeasurable

theorem circle_quarter_quadruple :
    (4 : ℕ) • (((1/4 : ℝ) : UnitCircle)) = 0 := by
  rw [← AddCircle.coe_nsmul]
  norm_num [nsmul_eq_mul, AddCircle.coe_period]

theorem circle_fourierCoeff_quarter_invariant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : UnitCircle → E)
    (hf : ∀ t, f (t + ((1/4 : ℝ) : UnitCircle)) = f t) (k : ℤ) :
    fourier (-k) (((1/4 : ℝ) : UnitCircle)) • fourierCoeff f k = fourierCoeff f k := by
  unfold fourierCoeff
  rw [← integral_smul]
  have h := integral_add_right_eq_self (μ := circleMeasure)
    (fun t : UnitCircle => fourier (-k) t • f t) (((1/4 : ℝ) : UnitCircle))
  calc
    _ = ∫ t, fourier (-k) (t+((1/4 : ℝ) : UnitCircle)) •
        f (t+((1/4 : ℝ) : UnitCircle)) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hf]
      simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, smul_smul]
      congr 1
      exact mul_comm _ _
    _ = _ := h

theorem circle_quarter_character_eq_one_iff (k : ℤ) :
    fourier k (((1/4 : ℝ) : UnitCircle)) = 1 ↔ ∃ j : ℤ, k = 4*j := by
  have hchar : fourier k (((1/4 : ℝ) : UnitCircle)) = 1 ↔
      k • (((1/4 : ℝ) : UnitCircle)) = 0 := by
    have hfour : fourier k (((1/4 : ℝ) : UnitCircle)) =
        (AddCircle.toCircle (k • (((1/4 : ℝ) : UnitCircle))) : ℂ) := rfl
    have hzero : (AddCircle.toCircle (0 : UnitCircle) : ℂ) = 1 := by simp
    constructor
    · intro h
      apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      apply Circle.coe_injective
      exact (hfour.symm.trans h).trans hzero.symm
    · intro h
      exact hfour.trans ((congrArg (fun q : UnitCircle =>
        (AddCircle.toCircle q : ℂ)) h).trans hzero)
  rw [hchar, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨j, hj⟩
    simp only [zsmul_eq_mul, mul_one] at hj
    refine ⟨j, ?_⟩
    have heq : (k : ℝ) = 4*(j : ℝ) := by linarith
    exact_mod_cast heq
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat]
    ring

theorem circle_fourierCoeff_quadruple_off {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : UnitCircle → E) (k : ℤ)
    (hk : ¬ ∃ j : ℤ, k = 4*j) :
    fourierCoeff (fun t => f (4 • t)) k = 0 := by
  have hinv : ∀ t : UnitCircle,
      f (4 • (t+((1/4 : ℝ) : UnitCircle))) = f (4 • t) := by
    intro t
    rw [smul_add, circle_quarter_quadruple, add_zero]
  have h := circle_fourierCoeff_quarter_invariant (fun t => f (4 • t)) hinv k
  have hc : fourier (-k) (((1/4 : ℝ) : UnitCircle)) ≠ 1 := by
    intro he
    obtain ⟨j, hj⟩ := (circle_quarter_character_eq_one_iff (-k)).mp he
    apply hk
    refine ⟨-j, ?_⟩
    linarith
  have hzero : (fourier (-k) (((1/4 : ℝ) : UnitCircle)) - 1) •
      fourierCoeff (fun t => f (4 • t)) k = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

theorem fourthRootCircleLift_fourierCoeff {r : ℕ}
    (U : ℝ → Circulation.Mat r)
    (hU : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) 1))) (k : ℤ) :
    matrixCircleFourierCoefficient (fourthRootCircleLift U) (4*k+1) =
      matrixCircleFourierCoefficient (intervalCircleLift U) k := by
  unfold matrixCircleFourierCoefficient fourthRootCircleLift
  rw [circle_fourier_modulation]
  simpa only [add_sub_cancel_right] using
    circle_fourierCoeff_quadruple _ (intervalCircleLift_integrable U hU) k

theorem fourthRootCircleLift_fourierCoeff_off {r : ℕ}
    (U : ℝ → Circulation.Mat r)
    (hU : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) 1))) (k : ℤ)
    (hk : ¬ ∃ j : ℤ, k = 4*j+1) :
    matrixCircleFourierCoefficient (fourthRootCircleLift U) k = 0 := by
  unfold matrixCircleFourierCoefficient fourthRootCircleLift
  rw [circle_fourier_modulation]
  apply circle_fourierCoeff_quadruple_off
  rintro ⟨j, hj⟩
  exact hk ⟨j, by linarith⟩

end
end CGLMPBounds.Hardy
