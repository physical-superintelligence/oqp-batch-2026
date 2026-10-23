module

public import ThreeCopyQutritWerner.CertificateCarrierPermutations

@[expose] public section



noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner




def certificateCarrierAction1_1 : Fin 12 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1, 0;
      0, 1],
    !![-1, -1;
      0, 1],
    !![1, 0;
      0, 1],
    !![-1, -1;
      0, 1],
    !![1, 0;
      0, 1],
    !![-1, -1;
      0, 1],
    !![1, 0;
      0, 1],
    !![-1, -1;
      0, 1],
    !![1, 0;
      0, 1],
    !![-1, -1;
      0, 1],
    !![1, 0;
      0, 1],
    !![-1, -1;
      0, 1]]

/-- Literal integer product of the original Gram and original carrier action. -/
def certificateCarrierWeightedAction1_1 : Fin 12 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1],
    !![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1],
    !![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1],
    !![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1],
    !![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1],
    !![2, 1;
      1, 2],
    !![-2, -1;
      -1, 1]]

end ThreeCopyQutritWerner
