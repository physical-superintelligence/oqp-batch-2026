module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-4, -1, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_02 :
    certificateDescendantBlockA2_02ᵀ * certificateDescendantBlockA2_02 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 5 => certificateDescendantGram2Index ⟨2, j⟩)
        (fun j : Fin 5 => certificateDescendantGram2Index ⟨2, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
