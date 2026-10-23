module

public import ThreeCopyQutritWerner.AppendixCInputs

@[expose] public section


/-! Definitional statement agreements between the Appendix C input statements. -/
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem appendixC_input1_statement_agreement : AppCInput1 =
(  ∀ (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (κ : ℂ), C.rank = 2 → C * C = κ • C →
    (frobSq C - 2 * Real.sqrt ((frobSq C ^ 2 - frobSq (Cᴴ * C)) / 2)) / 6 ≤ endpointEnergy C ∧
      (endpointEnergy C = 0 →
        ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₂₃ (Cᴴ * C)).rank ≤ 2) ∨
          ((ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (Cᴴ * C)).rank ≤ 2) ∨
            ((ptrace₁₂ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (Cᴴ * C)).rank ≤ 2))) := by
  rfl

theorem appendixC_input2_statement_agreement : AppCInput2 =
(  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank = 2 → endpointEnergy C = 0 →
    (∃ x : (Fin 3 × Fin 3 × Fin 3) → ℂ, C *ᵥ x ≠ 0 ∧ (∃ (u v w : Fin 3 → ℂ), ∀ p : Fin 3 × Fin 3 × Fin 3,
        (C *ᵥ x) p = u p.1 * v p.2.1 * w p.2.2)) →
      (ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2) := by
  rfl

theorem appendixC_input3_statement_agreement : AppCInput3 =
(  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2) → IsQutritZeroFamilyMember C) := by
  rfl

end ThreeCopyQutritWerner
