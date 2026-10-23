module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-2, 1, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_06 :
    certificateDescendantBlockA1_06ᵀ * certificateDescendantBlockA1_06 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 24 => certificateDescendantGram1Index ⟨6, j⟩)
        (fun j : Fin 24 => certificateDescendantGram1Index ⟨6, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
