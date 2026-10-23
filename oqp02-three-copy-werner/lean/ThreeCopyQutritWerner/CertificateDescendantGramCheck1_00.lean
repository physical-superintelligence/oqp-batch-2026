module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-3, 0, 3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_00 :
    certificateDescendantBlockA1_00ᵀ * certificateDescendantBlockA1_00 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 1 => certificateDescendantGram1Index ⟨0, j⟩)
        (fun j : Fin 1 => certificateDescendantGram1Index ⟨0, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
