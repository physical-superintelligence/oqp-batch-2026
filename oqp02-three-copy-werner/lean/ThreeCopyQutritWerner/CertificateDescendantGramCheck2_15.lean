module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-1, -3, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_15 :
    certificateDescendantBlockA2_15ᵀ * certificateDescendantBlockA2_15 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 35 => certificateDescendantGram2Index ⟨15, j⟩)
        (fun j : Fin 35 => certificateDescendantGram2Index ⟨15, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
