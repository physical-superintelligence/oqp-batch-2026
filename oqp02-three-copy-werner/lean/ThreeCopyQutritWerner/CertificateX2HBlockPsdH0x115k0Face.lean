module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Holomorphic block `115-0`: exact positivity of its face block `A = Kᵀ N K`
(2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x115k0Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![594345747769074769733439948751102214483042366515126359601993728, 437773492643363513473396724204447665712350246623629836611517440;
    437773492643363513473396724204447665712350246623629836611517440, 62257325932374249515562702242333050537480572002104578222880081920]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![42226025663176309744967730674388, 0;
    41469542611975335534710966190247, 496704373865664167817571769731425]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1783037243307224309200319846253330555870349093931495453279174544, 1751093970573454053893586896817782950333584527760714796418293836;
    1751093970573454053893586896817782950333584527760714796418293836, 248434957981727923292517369020580852250577251837321694150030451634]

theorem CC_eq : C * Cᵀ = CC := by decide +kernel

theorem residual_symm : ((2 : ℤ) ^ 2 • A - CC)ᵀ = (2 : ℤ) ^ 2 • A - CC := by decide +kernel

theorem residual_rows : ∀ i, ∑ j ∈ Finset.univ.erase i, |((2 : ℤ) ^ 2 • A - CC) i j| ≤
    ((2 : ℤ) ^ 2 • A - CC) i i := by decide +kernel

/-- The face block is positive semidefinite (exact). -/
theorem A_psd : (A.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_residual A CC 2 (by norm_num)
    (by rw [← CC_eq]; exact certificateX2_int_gram_posSemidef C) residual_symm residual_rows

/-- The rational face block `(1/den) • A` (`den = 57735991281730516779464839149788173726453690037306728120320000`), in the bridge's `x2Complex` form. -/
theorem A_psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • A.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef A 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) A_psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x115k0Face
