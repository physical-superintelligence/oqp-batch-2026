module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-1, -2, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_16 :
    certificateDescendantBlockA2_16ᵀ * certificateDescendantBlockA2_16 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 80 => certificateDescendantGram2Index ⟨16, j⟩)
        (fun j : Fin 80 => certificateDescendantGram2Index ⟨16, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
