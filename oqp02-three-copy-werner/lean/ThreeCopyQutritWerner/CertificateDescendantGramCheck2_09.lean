module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-2, -3, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_09 :
    certificateDescendantBlockA2_09ᵀ * certificateDescendantBlockA2_09 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 10 => certificateDescendantGram2Index ⟨9, j⟩)
        (fun j : Fin 10 => certificateDescendantGram2Index ⟨9, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
