module

public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-! Holomorphic block `036-0`: exact positivity of its face block `A = Kᵀ N K`
(2 x 2). `C` is an approximate Cholesky factor of `A` at scale `t = 2^1`; the kernel checks
`C Cᵀ = CC` and that `t² A - CC` is symmetric and row dominant. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x036k0Face

def A : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1021879131590134024364577660347250641972259274993792170771861504, -387366873613174526595121358403608530606233245756298314237540352;
    -387366873613174526595121358403608530606233245756298314237540352, 413354801652207555653035542131161805373298744752535438185970944]

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![61814254666900819785074530583791, 0;
    -25066507762688902308751020865340, 27542239358044597916252138915067]

def CC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3821002080024469778762348314878906774911550621017790227271931681, -1549467494452698106380485433614416388087874274065061012197703940;
    -1549467494452698106380485433614416388087874274065061012197703940, 1386904760272763903916179842014558146428046351182851206252930089]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x036k0Face
