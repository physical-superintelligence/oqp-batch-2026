module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-2, -1, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_11 :
    certificateDescendantBlockA2_11ᵀ * certificateDescendantBlockA2_11 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 80 => certificateDescendantGram2Index ⟨11, j⟩)
        (fun j : Fin 80 => certificateDescendantGram2Index ⟨11, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
