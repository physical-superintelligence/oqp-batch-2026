module

public import CGLMPBounds.Hardy.PoissonBoundaryMean
public import CGLMPBounds.Hardy.CircularHilbertPinching

@[expose] public section


/-! Actual C.16 fourth-root data satisfy every hypothesis of the proved
Poisson boundary mean. Matrix integrals are transferred through scalar
entries, retaining the distinction between Pi and Hilbert operator norms. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Entrywise
open scoped Matrix.Norms.Elementwise
local instance fourthRootBoundaryMeanENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

lemma fourthRootCircleB_entries_memLp {r : ℕ}
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ*U t=1)
    (i j : Fin r) : MemLp (fun t => fourthRootCircleB U t i j) 2 circleMeasure :=
  (((fourthRootCircle_parts_memLp U hU hunit).2.eval i).eval j)

lemma fourthRootCircleB_entry_mean_zero {r : ℕ} (hr : 0 < r)
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ*U t=1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t^4=Complex.exp (((-2*Real.pi*t : ℝ) : ℂ)*Complex.I) • (1 : Circulation.Mat r))
    (i j : Fin r) : (∫ t, fourthRootCircleB U t i j ∂circleMeasure)=0 := by
  have hi := (fourthRootCircle_parts_memLp U hU hunit).2.integrable (by norm_num)
  have h := congrArg (fun X : Circulation.Mat r => X i j)
    (fourthRootCircle_involutions hr U hU hunit hfour).2.2
  have he : (∫ t, fourthRootCircleB U t ∂circleMeasure) i j =
      ∫ t, fourthRootCircleB U t i j ∂circleMeasure := by
    let L : Circulation.Mat r →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj i : (Fin r → Fin r → ℂ) →L[ℂ] (Fin r → ℂ))
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
      using! (L.integral_comp_comm hi).symm
  rw [he] at h
  simpa only [Matrix.zero_apply] using h
end Entrywise

section Operator
open scoped Matrix.Norms.L2Operator

theorem fourthRootCircle_boundary_potential_mean {r : ℕ} (hr : 0 < r)
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ*U t=1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t^4=Complex.exp (((-2*Real.pi*t : ℝ) : ℂ)*Complex.I) • (1 : Circulation.Mat r)) :
    Integrable (fun t => matrixHardyPotential
      (fourthRootCircleB U t+Complex.I • matrixHilbert (fourthRootCircleB U) t)) circleMeasure ∧
    (∫ t, matrixHardyPotential
      (fourthRootCircleB U t+Complex.I • matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure)=
      hardyStripCenterConstant := by
  letI : NeZero r := ⟨ne_of_gt hr⟩
  have hB := matrix_memLp_of_entries (fourthRootCircleB_entries_memLp U hU hunit)
  have hinv := (fourthRootCircle_involutions hr U hU hunit hfour).1
  apply matrixPoisson_boundary_potential_mean hr (fourthRootCircleB U) hB.aestronglyMeasurable
    (hinv.mono (fun _ h => h.2.1))
  · filter_upwards [hinv] with t ht
    exact le_of_eq (CStarRing.norm_of_mem_unitary
      (hermitian_involution_mem_unitary ht.2.1 ht.2.2.2.1))
  · ext i j
    rw [matrix_integral_entry (hB.integrable (by norm_num)),
      fourthRootCircleB_entry_mean_zero hr U hU hunit hfour]
    rfl

end Operator
end
end CGLMPBounds.Hardy
