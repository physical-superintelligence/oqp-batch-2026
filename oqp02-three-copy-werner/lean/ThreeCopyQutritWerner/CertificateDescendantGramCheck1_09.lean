module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-1, -2, 3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_09 :
    certificateDescendantBlockA1_09ᵀ * certificateDescendantBlockA1_09 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 3 => certificateDescendantGram1Index ⟨9, j⟩)
        (fun j : Fin 3 => certificateDescendantGram1Index ⟨9, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
