module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Corrected source block `1-116-0`: exact positivity of its corrected face block
`A / den = Z Zᵀ / 2^160 + C` (trial plus exact correction, kernel coordinates; `A` below is its numerator,
2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2Correction1x116k0Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![23235035785124851752442710730365392723020005357611899944960, -40359026042655666543660204646404522765445397412902338560000;
    -40359026042655666543660204646404522765445397412902338560000, 70121592385150254285787944509949607824236984584019902464000]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![304853328244322551466222312035, 0;
    -529553359644611910580025524630, 7417373581436600344852676808]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![92935551741640669899551811978413255396381646809260905841225, -161436104170622666174640818585710025343633109112312437922050;
    -161436104170622666174640818585710025343633109112312437922050, 280481778141742280032932747097184993932630410123949637705764]

theorem CC_eq : C * Cᵀ = CC := by decide +kernel

theorem residual_symm : ((2 : ℤ) ^ 2 • A - CC)ᵀ = (2 : ℤ) ^ 2 • A - CC := by decide +kernel

theorem residual_rows : ∀ i, ∑ j ∈ Finset.univ.erase i, |((2 : ℤ) ^ 2 • A - CC) i j| ≤
    ((2 : ℤ) ^ 2 • A - CC) i i := by decide +kernel

/-- The face block is positive semidefinite (exact). -/
theorem A_psd : (A.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_residual A CC 2 (by norm_num)
    (by rw [← CC_eq]; exact certificateX2_int_gram_posSemidef C) residual_symm residual_rows

/-- The rational face block `(1/den) • A` (`den = 46188793025384413423571871319830538981162952029845382496256000`), in the bridge's `x2Complex` form. -/
theorem A_psd_rat : (((1 / ((46188793025384413423571871319830538981162952029845382496256000 : ℤ) : ℚ)) • A.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef A 46188793025384413423571871319830538981162952029845382496256000 (by norm_num) A_psd

end ThreeCopyQutritWerner.X2Correction1x116k0Face
