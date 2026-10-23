module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, -3, -2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_29 :
    certificateDescendantBlockA2_29ᵀ * certificateDescendantBlockA2_29 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 10 => certificateDescendantGram2Index ⟨29, j⟩)
        (fun j : Fin 10 => certificateDescendantGram2Index ⟨29, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
