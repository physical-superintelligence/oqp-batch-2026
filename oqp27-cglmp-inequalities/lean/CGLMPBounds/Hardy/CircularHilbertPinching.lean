module

public import CGLMPBounds.Hardy.FourthRootHilbertPairing
public import CGLMPBounds.Hardy.HermitianPinchingTraceBound
public import CGLMPBounds.Hardy.MatrixAbsoluteIntegrability

@[expose] public section


/-! The inequality in literal C.16, including integrability of its actual
absolute trace. No conditional positivity or domination premise is used. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance circularHilbertPinchingUnitPeriod : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance circularHilbertPinchingENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem unitary_function_entry_memLp_top {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (hB : AEStronglyMeasurable B circleMeasure)
    (hunit : ∀ᵐ t ∂circleMeasure, (B t)ᴴ*B t=1) (i j : Fin r) :
    MemLp (fun t => B t i j) ⊤ circleMeasure := by
  apply memLp_top_of_bound
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hB)) 1
  filter_upwards [hunit] with t ht
  exact unitary_entry_norm_le_one (⟨B t, Matrix.mem_unitaryGroup_iff'.mpr ht⟩) i j

theorem unitary_left_matrix_memLp {r : ℕ} (B Y : UnitCircle → Circulation.Mat r)
    (hB : AEStronglyMeasurable B circleMeasure)
    (hunit : ∀ᵐ t ∂circleMeasure, (B t)ᴴ*B t=1)
    (hY : MemLp Y 2 circleMeasure) :
    MemLp (fun t => B t*Y t) 2 circleMeasure := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  exact (unitary_function_entry_memLp_top B hB hunit i k).mul ((hY.eval k).eval j)

theorem unitary_right_matrix_memLp {r : ℕ} (B Y : UnitCircle → Circulation.Mat r)
    (hB : AEStronglyMeasurable B circleMeasure)
    (hunit : ∀ᵐ t ∂circleMeasure, (B t)ᴴ*B t=1)
    (hY : MemLp Y 2 circleMeasure) :
    MemLp (fun t => Y t*B t) 2 circleMeasure := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  exact ((hY.eval i).eval k).mul (unitary_function_entry_memLp_top B hB hunit k j)

theorem unitary_pinching_memLp {r : ℕ} (B Y : UnitCircle → Circulation.Mat r)
    (hB : AEStronglyMeasurable B circleMeasure)
    (hunit : ∀ᵐ t ∂circleMeasure, (B t)ᴴ*B t=1)
    (hY : MemLp Y 2 circleMeasure) :
    MemLp (fun t => positivePinchingPart (B t) (Y t)) 2 circleMeasure := by
  have hYB := unitary_right_matrix_memLp B Y hB hunit hY
  have hBYB := unitary_left_matrix_memLp B (fun t => Y t*B t) hB hunit hYB
  convert! (hY.add hBYB).const_smul (1/2 : ℂ) using 1
  funext t
  simp only [positivePinchingPart, Matrix.mul_assoc, Pi.smul_apply, Pi.add_apply]

theorem fourthRootCircle_hilbert_pinching_bound {r : ℕ} (hr : 0 < r)
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r)) :
    Integrable (fun t => normalizedMatrixAbsTrace
      (positivePinchingPart (fourthRootCircleB U t)
        (matrixHilbert (fourthRootCircleB U) t))) circleMeasure ∧
    (∫ t, Circulation.reTr
      (fourthRootCircleA U t * matrixHilbert (fourthRootCircleB U) t) ∂circleMeasure) ≤
    ∫ t, normalizedMatrixAbsTrace
      (positivePinchingPart (fourthRootCircleB U t)
        (matrixHilbert (fourthRootCircleB U) t)) ∂circleMeasure := by
  obtain ⟨hA,hB⟩ := fourthRootCircle_parts_memLp U hU hunit
  have hinv := (fourthRootCircle_involutions hr U hU hunit hfour).1
  have hBu : ∀ᵐ t ∂circleMeasure,
      (fourthRootCircleB U t)ᴴ*fourthRootCircleB U t=1 := by
    filter_upwards [hinv] with t ht
    rw [ht.2.1.eq, ← pow_two, ht.2.2.2.1]
  have hBY := unitary_pinching_memLp _ _ hB.aestronglyMeasurable hBu
    (matrixHilbert_memLp (fourthRootCircleB U))
  have hi := normalizedMatrixAbsTrace_integrable _ hBY
  refine ⟨hi, integral_mono_ae
    (fourthRootCircle_hilbert_pairing hr U hU hunit hfour).1 hi ?_⟩
  have hHB := matrixHilbert_hermitian_ae (fourthRootCircleB U) hB
    (hinv.mono (fun _ h => h.2.1))
  filter_upwards [hinv,hHB] with t ht hHt
  exact hermitian_involution_pinching_trace_bound _ _ _ ht.1 ht.2.2.1 ht.2.1
    ht.2.2.2.1 hHt ht.2.2.2.2

end
end CGLMPBounds.Hardy
