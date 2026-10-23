module

public import ThreeCopyQutritWerner.CertificateCarrierPermutations

@[expose] public section



noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner




def certificateCarrierAction1_0 : Fin 12 → Matrix (Fin 1) (Fin 1) ℤ :=
  ![!![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1]]

/-- Literal integer product of the original Gram and original carrier action. -/
def certificateCarrierWeightedAction1_0 : Fin 12 → Matrix (Fin 1) (Fin 1) ℤ :=
  ![!![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1]]

end ThreeCopyQutritWerner
