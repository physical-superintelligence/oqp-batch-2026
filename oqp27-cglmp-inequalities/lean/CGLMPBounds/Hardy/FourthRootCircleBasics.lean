module

public import CGLMPBounds.Hardy.CircleEnergySplit
public import CGLMPBounds.Hardy.CircleMatrixL2
public import CGLMPBounds.Hardy.FourthRootHermitianInvolutions
public import CGLMPBounds.Quantum.UnitaryCompact

@[expose] public section


/-! The actual W(s)=sU(s⁴) is unitary and a fourth root almost everywhere;
its literal A/B parts are L² and have zero means. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance fourthRootCircleBasicsUnitPeriod : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance fourthRootCircleBasicsENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem unitary_function_memLp {r : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (F : α → Circulation.Mat r)
    (hF : AEStronglyMeasurable F μ) (hunit : ∀ᵐ t ∂μ, (F t)ᴴ * F t = 1) :
    MemLp F 2 μ := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  apply MemLp.of_bound
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hF)) 1
  filter_upwards [hunit] with t ht
  exact unitary_entry_norm_le_one (⟨F t, Matrix.mem_unitaryGroup_iff'.mpr ht⟩) i j

theorem fourthRootCircleLift_aestronglyMeasurable {r : ℕ}
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    AEStronglyMeasurable (fourthRootCircleLift U) circleMeasure := by
  have hrep := hU.comp_measurePreserving circle_representative_measurePreserving
  have hrep' : AEStronglyMeasurable (intervalCircleLift U) circleMeasure := by
    simpa only [intervalCircleLift, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def] using hrep
  exact (fourier 1).continuous.aestronglyMeasurable.smul
    (hrep'.comp_measurePreserving circle_quadruple_measurePreserving)

theorem fourthRootCircleLift_unitary {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) :
    ∀ᵐ t ∂circleMeasure,
      (fourthRootCircleLift U t)ᴴ * fourthRootCircleLift U t = 1 := by
  have hlift : ∀ᵐ t ∂circleMeasure,
      (intervalCircleLift U t)ᴴ * intervalCircleLift U t = 1 := by
    simpa only [intervalCircleLift, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def] using
      circle_representative_measurePreserving.quasiMeasurePreserving.ae hunit
  have hquad := circle_quadruple_measurePreserving.quasiMeasurePreserving.ae hlift
  filter_upwards [hquad] with t ht
  have hp : fourier 1 t * star (fourier 1 t) = 1 := by
    simp only [Complex.star_def, ← fourier_neg, ← fourier_add]
    norm_num
  simp only [fourthRootCircleLift, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ht, hp, one_smul]

theorem circle_fourier_pow (k : ℤ) (n : ℕ) (t : UnitCircle) :
    (fourier k t)^n = fourier ((n : ℤ)*k) t := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← fourier_add]
    congr 1
    push_cast
    ring

theorem fourthRootCircleLift_fourthPower {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r)) :
    ∀ᵐ t ∂circleMeasure, fourthRootCircleLift U t ^ 4 = 1 := by
  have hlift : ∀ᵐ t ∂circleMeasure,
      intervalCircleLift U t ^ 4 = fourier (-1) t • (1 : Circulation.Mat r) := by
    have h := circle_representative_measurePreserving.quasiMeasurePreserving.ae hfour
    filter_upwards [h] with t ht
    change (U (AddCircle.equivIoc 1 0 t : ℝ))^4 = _
    rw [ht]
    congr 1
    have hrep : (((AddCircle.equivIoc 1 0 t : ℝ) : UnitCircle)) = t := AddCircle.coe_equivIoc
    conv_rhs => rw [← hrep, fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hquad := circle_quadruple_measurePreserving.quasiMeasurePreserving.ae hlift
  filter_upwards [hquad] with t ht
  simp only [fourthRootCircleLift, smul_pow, ht, smul_smul, circle_fourier_pow,
    circle_fourier_quadruple, ← fourier_add]
  norm_num

theorem fourthRootCircleLift_memLp {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) :
    MemLp (fourthRootCircleLift U) 2 circleMeasure :=
  unitary_function_memLp _ (fourthRootCircleLift_aestronglyMeasurable U hU)
    (fourthRootCircleLift_unitary U hunit)

theorem fourthRootCircle_parts_memLp {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) :
    MemLp (fourthRootCircleA U) 2 circleMeasure ∧ MemLp (fourthRootCircleB U) 2 circleMeasure := by
  have hW := fourthRootCircleLift_memLp U hU hunit
  have hWs := matrix_conjTranspose_memLp _ hW
  have hR := (hW.add hWs).const_smul (1/2 : ℂ)
  have hI := (hW.sub hWs).const_smul (-Complex.I/2)
  exact ⟨hR.add hI, hR.sub hI⟩

theorem fourthRootCircleLift_mean_zero {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∫ t, fourthRootCircleLift U t ∂circleMeasure) = 0 := by
  have h := fourthRootCircleLift_fourierCoeff_off U hU 0 (by rintro ⟨j, hj⟩; omega)
  simpa only [matrixCircleFourierCoefficient, fourierCoeff, neg_zero,
    fourier_zero, one_smul] using h

theorem fourthRootCircle_involutions {r : ℕ} (hr : 0 < r) (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r)) :
    (∀ᵐ t ∂circleMeasure,
      (fourthRootCircleA U t).IsHermitian ∧ (fourthRootCircleB U t).IsHermitian ∧
      fourthRootCircleA U t ^ 2 = 1 ∧ fourthRootCircleB U t ^ 2 = 1 ∧
      fourthRootCircleA U t * fourthRootCircleB U t =
        fourthRootCircleB U t * fourthRootCircleA U t) ∧
    (∫ t, fourthRootCircleA U t ∂circleMeasure) = 0 ∧
    (∫ t, fourthRootCircleB U t ∂circleMeasure) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [fourthRootCircleLift_unitary U hunit,
      fourthRootCircleLift_fourthPower U hfour] with t ht ht4
    exact fourthRoot_hermitian_parts _ ht ht4
  all_goals
    have hW := fourthRootCircleLift_memLp U hU hunit
    have hWs := matrix_conjTranspose_memLp _ hW
    have hi := hW.integrable (by norm_num)
    have his := hWs.integrable (by norm_num)
    have hz := fourthRootCircleLift_mean_zero U
      ((unitary_function_memLp U hU hunit).integrable (by norm_num))
    have hzs : (∫ t, (fourthRootCircleLift U t)ᴴ ∂circleMeasure) = 0 := by
      rw [matrix_integral_conjTranspose _ hW, hz, Matrix.conjTranspose_zero]
    simp only [fourthRootCircleA, fourthRootCircleB, hermitianRealPart, hermitianImagPart]
    simp only [integral_add (Integrable.fun_smul (1/2 : ℂ) (hi.fun_add his))
      (Integrable.fun_smul (-Complex.I/2) (hi.sub' his)),
      integral_sub (Integrable.fun_smul (1/2 : ℂ) (hi.fun_add his))
        (Integrable.fun_smul (-Complex.I/2) (hi.sub' his)), integral_smul,
      integral_add hi his, integral_sub hi his, hz, hzs, add_zero, sub_zero,
      smul_zero]

end
end CGLMPBounds.Hardy
