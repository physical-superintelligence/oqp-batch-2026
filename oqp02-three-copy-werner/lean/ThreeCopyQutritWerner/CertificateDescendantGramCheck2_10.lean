module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-2, -2, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_10 :
    certificateDescendantBlockA2_10ᵀ * certificateDescendantBlockA2_10 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 50 => certificateDescendantGram2Index ⟨10, j⟩)
        (fun j : Fin 50 => certificateDescendantGram2Index ⟨10, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
