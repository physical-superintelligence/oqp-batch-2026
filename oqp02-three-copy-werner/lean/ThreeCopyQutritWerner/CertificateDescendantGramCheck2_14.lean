module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-1, -4, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_14 :
    certificateDescendantBlockA2_14ᵀ * certificateDescendantBlockA2_14 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 5 => certificateDescendantGram2Index ⟨14, j⟩)
        (fun j : Fin 5 => certificateDescendantGram2Index ⟨14, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
