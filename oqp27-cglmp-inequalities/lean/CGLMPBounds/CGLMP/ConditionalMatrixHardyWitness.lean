module

public import CGLMPBounds.CGLMP.ConditionalMatrixHardyBell
public import CGLMPBounds.CGLMP.LocalBound

@[expose] public section


/-! Equation(A.5) of TheoremA.3, with its precise witness-threshold equality
classification, from the general matrix Hardy bound C.6 as a hypothesis
(`hC6`). `CGLMP/WitnessTolerance.lean` discharges it with the proved
`Hardy.fourth_root_matrix_Hardy_bound`. -/
namespace CGLMPBounds
open MeasureTheory Matrix
open scoped Kronecker
noncomputable section

variable (hC6 : ∀ {r : ℕ}, 0 < r → ∀ U : ℝ → Circulation.Mat r,
  AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)) →
  (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) →
  (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
    U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
      (1 : Circulation.Mat r)) →
  Partition.sourceFourthRootHardyConstant ≤ Partition.matrixNegativeFourierEnergy U)
include hC6

theorem cglmp_witness_tolerance_of_matrixHardy_input
    {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, IsPVM (P t))
    (hviolation : 2 < cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3])) :
    let q := tracialTable ![P 0,P 2] ![P 1,P 3]
    (∀ v : ℝ, 2 < cglmp d (noisy v q) ↔ 2 / cglmp d q < v) ∧
    2 / cglmpFourierValue d ≤ 2 / cglmp d q ∧
    (2 / cglmp d q = 2 / cglmpFourierValue d ↔
      ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
        n = d*k ∧ U*Uᴴ=1 ∧ Uᴴ*U=1 ∧
        ∀ (t : Fin 4) (a : ZMod d), P t a =
          U * (fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ) := by
  dsimp only
  have hbound := cglmp_projective_bound_of_matrixHardy_input hC6 hd P hP
  have hq : 0 < cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) := by linarith
  have hF : 0 < cglmpFourierValue d := hq.trans_le hbound
  refine ⟨two_lt_cglmp_noisy_iff d hd hviolation, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (by norm_num) hq hbound
  · rw [← cglmp_eq_fourier_iff_standard_of_matrixHardy_input hC6 hd P hP]
    constructor
    · intro heq
      have hcross := (div_eq_div_iff hq.ne' hF.ne').mp heq
      linarith
    · intro heq
      rw [heq]

end
end CGLMPBounds
