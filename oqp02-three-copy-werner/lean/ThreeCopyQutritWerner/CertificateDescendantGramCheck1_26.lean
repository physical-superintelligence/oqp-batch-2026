module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [1, 1, -2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_26 :
    certificateDescendantBlockA1_26ᵀ * certificateDescendantBlockA1_26 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 24 => certificateDescendantGram1Index ⟨26, j⟩)
        (fun j : Fin 24 => certificateDescendantGram1Index ⟨26, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
