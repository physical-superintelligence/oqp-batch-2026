module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-1, 0, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_11 :
    certificateDescendantBlockA1_11ᵀ * certificateDescendantBlockA1_11 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 60 => certificateDescendantGram1Index ⟨11, j⟩)
        (fun j : Fin 60 => certificateDescendantGram1Index ⟨11, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
