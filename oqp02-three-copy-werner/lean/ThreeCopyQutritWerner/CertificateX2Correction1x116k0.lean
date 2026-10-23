module

public import ThreeCopyQutritWerner.CertificateX2Correction1x116k0Face

@[expose] public section


/-! Corrected source block `1-116-0`: the J-coordinate coefficient block
`K (A / den) Kᵀ` (9 x 9; face dimension 2) is positive semidefinite, where `A / den` is the
corrected face block `Z Zᵀ / 2^160 + C` (trial plus exact correction) and `K` is
the block's forced kernel. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2Correction1x116k0

open ThreeCopyQutritWerner.X2Correction1x116k0Face

/-- The forced kernel of block `1-116-0` (J coordinates x face coordinates). -/
def K : Matrix (Fin 9) (Fin 2) ℤ :=
  !![1, 0;
    0, 1;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0]

/-- The corrected J-coordinate coefficient block `K (A / den) Kᵀ` is positive semidefinite. -/
theorem jblock_psd : (((K.map (Int.cast : ℤ → ℚ)) * ((1 / ((46188793025384413423571871319830538981162952029845382496256000 : ℤ) : ℚ)) • A.map (Int.cast : ℤ → ℚ)) *
    (K.map (Int.cast : ℤ → ℚ))ᵀ).map (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_congr_posSemidef _ _ A_psd_rat

end ThreeCopyQutritWerner.X2Correction1x116k0
