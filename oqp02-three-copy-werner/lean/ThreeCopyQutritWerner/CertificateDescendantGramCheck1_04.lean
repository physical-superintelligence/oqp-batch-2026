module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-2, -1, 3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_04 :
    certificateDescendantBlockA1_04ᵀ * certificateDescendantBlockA1_04 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 3 => certificateDescendantGram1Index ⟨4, j⟩)
        (fun j : Fin 3 => certificateDescendantGram1Index ⟨4, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
