module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, 0, -5]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_32 :
    certificateDescendantBlockA2_32ᵀ * certificateDescendantBlockA2_32 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 1 => certificateDescendantGram2Index ⟨32, j⟩)
        (fun j : Fin 1 => certificateDescendantGram2Index ⟨32, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
