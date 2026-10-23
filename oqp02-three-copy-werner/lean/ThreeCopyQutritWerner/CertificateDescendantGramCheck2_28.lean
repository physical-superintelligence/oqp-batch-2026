module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, -4, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_28 :
    certificateDescendantBlockA2_28ᵀ * certificateDescendantBlockA2_28 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 5 => certificateDescendantGram2Index ⟨28, j⟩)
        (fun j : Fin 5 => certificateDescendantGram2Index ⟨28, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
