module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [1, -3, 2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_22 :
    certificateDescendantBlockA1_22ᵀ * certificateDescendantBlockA1_22 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 3 => certificateDescendantGram1Index ⟨22, j⟩)
        (fun j : Fin 3 => certificateDescendantGram1Index ⟨22, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
