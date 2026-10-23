module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, 1, -5]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_26 :
    certificateDescendantBlockA2_26ᵀ * certificateDescendantBlockA2_26 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 1 => certificateDescendantGram2Index ⟨26, j⟩)
        (fun j : Fin 1 => certificateDescendantGram2Index ⟨26, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
