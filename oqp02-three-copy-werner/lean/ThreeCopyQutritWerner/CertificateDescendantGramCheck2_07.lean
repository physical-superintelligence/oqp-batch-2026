module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-3, 0, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_07 :
    certificateDescendantBlockA2_07ᵀ * certificateDescendantBlockA2_07 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 35 => certificateDescendantGram2Index ⟨7, j⟩)
        (fun j : Fin 35 => certificateDescendantGram2Index ⟨7, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
