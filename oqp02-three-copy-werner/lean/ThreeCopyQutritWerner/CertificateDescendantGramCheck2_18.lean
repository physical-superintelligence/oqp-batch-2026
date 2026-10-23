module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-1, 0, -3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_18 :
    certificateDescendantBlockA2_18ᵀ * certificateDescendantBlockA2_18 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 35 => certificateDescendantGram2Index ⟨18, j⟩)
        (fun j : Fin 35 => certificateDescendantGram2Index ⟨18, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
