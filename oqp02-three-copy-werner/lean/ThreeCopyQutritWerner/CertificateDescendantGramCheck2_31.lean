module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, -1, -4]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_31 :
    certificateDescendantBlockA2_31ᵀ * certificateDescendantBlockA2_31 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 5 => certificateDescendantGram2Index ⟨31, j⟩)
        (fun j : Fin 5 => certificateDescendantGram2Index ⟨31, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
