module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-3, 1, 2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_01 :
    certificateDescendantBlockA1_01ᵀ * certificateDescendantBlockA1_01 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 3 => certificateDescendantGram1Index ⟨1, j⟩)
        (fun j : Fin 3 => certificateDescendantGram1Index ⟨1, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
