module

public import CGLMPBounds.Companion.CutStandardizationZero
public import CGLMPBounds.Companion.FiniteCoordinates
public import CGLMPBounds.CGLMP.FourierDescent

@[expose] public section


/-!
# Descending zero forbidden mass in the actual finite companion coordinates

The source definitions of C.4 are identified with the block-clock construction.
Consequently a fourth-root companion with literal F_d=0 standardizes, and every
actual common reducing original strategy is a standard amplification. The
analytic implication from Bell saturation to F_d=0 remains a separate obligation.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds.Companion
noncomputable section
variable {d n : ℕ} [NeZero d] [NeZero n]

lemma finite_fourierLift_eq_block :
    CompanionFinite.fourierLift d n = liftedFourier (d := d) (ι := Fin (4 * n)) := by
  have hF : CompanionFinite.fourierMatrix d = outcomeFourier (d := d) := by
    ext a j
    exact (outcomeFourier_apply a j).symm
  unfold CompanionFinite.fourierLift liftedFourier
  rw [hF]

lemma finite_clock_eq_block (V : CompanionFinite.Tuple d n) :
    CompanionFinite.clock V = blockFourierOperator
      (fun j => sourcePhase j • (V j : CompanionFinite.MultiplicityMat n)) := by
  have hD : CompanionFinite.frequencyOperator V = frequencyDiagonal
      (fun j => sourcePhase j • (V j : CompanionFinite.MultiplicityMat n)) := by
    change Matrix.compRingEquiv (Fin d) (Fin (4 * n)) ℂ
        (Matrix.diagonal fun j => CompanionFinite.phase j •
          (V j : CompanionFinite.MultiplicityMat n)) =
      Matrix.compRingEquiv (Fin d) (Fin (4 * n)) ℂ
        (Matrix.diagonal fun j => sourcePhase j •
          (V j : CompanionFinite.MultiplicityMat n))
    simp only [sourcePhase_eq_finite]
  unfold CompanionFinite.clock blockFourierOperator
  rw [finite_fourierLift_eq_block, hD]

lemma finite_measurement_eq_block (V : CompanionFinite.Tuple d n)
    (t : Fin 4) (a : ZMod d) :
    CompanionFinite.measurement V t a = blockClockMeasurement
      (blockFourierOperator
        (fun j => sourcePhase j • (V j : CompanionFinite.MultiplicityMat n))) t.val a := by
  unfold CompanionFinite.measurement blockClockMeasurement
  rw [finite_clock_eq_block]
  rfl

/-- The actual C.4 measurements standardize from the literal zero forbidden mass. -/
theorem finite_standardization_of_forbidden_zero (V : CompanionFinite.Tuple d n)
    (hfour : ∀ j, (V j : CompanionFinite.MultiplicityMat n) ^ 4 = 1)
    (hzero : scalarForbiddenTotal
      (fun j => (V j : CompanionFinite.MultiplicityMat n)) = 0) :
    ∃ T : Matrix (CompanionFinite.Physical d n) (Fin d × Fin (4 * n)) ℂ,
      Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧
      ∀ (t : Fin 4) (a : ZMod d),
        CompanionFinite.measurement V t a = T *
          (fourierProjector d t.val a ⊗ₖ (1 : CompanionFinite.MultiplicityMat n)) * Tᴴ := by
  obtain ⟨T, hT, hT', hstd⟩ := exists_standardization_of_forbidden_zero
    (fun j => (V j : CompanionFinite.MultiplicityMat n))
    (fun j => (V j).property.1) hfour hzero
  refine ⟨T, hT, hT', ?_⟩
  intro t a
  rw [finite_measurement_eq_block]
  exact hstd t a

/-- E.1's full original-space conclusion once the actual companion has F_d=0.
The isometry and intertwining use the literal C.4 measurements, not a surrogate. -/
theorem finite_reducing_standard_of_forbidden_zero
    (P : Fin 4 → ZMod d → Base n) (V : CompanionFinite.Tuple d n)
    (hfour : ∀ j, (V j : CompanionFinite.MultiplicityMat n) ^ 4 = 1)
    (hzero : scalarForbiddenTotal
      (fun j => (V j : CompanionFinite.MultiplicityMat n)) = 0)
    (Z : Matrix (CompanionFinite.Physical d n) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (hinter : ∀ t a, CompanionFinite.measurement V t a * Z = Z * P t a)
    (hcomm : ∀ t a, Commute (CompanionFinite.measurement V t a) (Z * Zᴴ)) :
    ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
      n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      ∀ (t : Fin 4) (a : ZMod d),
        P t a = U * (fourierProjector d t.val a ⊗ₖ
          (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ := by
  obtain ⟨T, hT, hT', hstd⟩ := finite_standardization_of_forbidden_zero V hfour hzero
  exact standard_fourier_descent d (CompanionFinite.measurement V) P
    T hT hT' hstd Z hZ hinter hcomm

end
end CGLMPBounds.Companion
