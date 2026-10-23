module

public import ThreeCopyQutritWerner.CertificateX2IntegrationSourcesSymm
public import ThreeCopyQutritWerner.CertificateX2InputGlueV

@[expose] public section


/-!
# Trial blocks through the packed factor `X2.x2FactorOf`

`x2TrialFactor s b` is definitionally `X2.x2FactorOf (x2KeySize s b) (x2FaceDim s b) (X2.x2TrialAll.getD g [])`
(`g = x2KeyGlobal s b`), so every trial block is `((1 / 2 ^ 80 : ℚ) • F.map Int.cast) * (same)ᵀ` with that `F`: the form of
the hypotheses `hN` of the input-stage lemmas (CertificateX2InputGlueKey, CertificateX2InputSlice016).
With `x2SourceM_of_not_mem` / `x2SourceA_of_not_mem` this gives them for every uncorrected key of `x2SourceM` / `x2SourceA`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem x2TrialFactor_eq_factorOf (s : Fin 3) (b : x2Key s) :
    x2TrialFactor s b =
      X2.x2FactorOf (x2KeySize s b) (x2FaceDim s b) (X2.x2TrialAll.getD ((x2KeyGlobal s b : Fin 414) : ℕ) []) :=
  rfl

/-- The trial block in the form. -/
theorem x2Trial_eq_factorOf (s : Fin 3) (b : x2Key s) :
    x2Trial s b =
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize s b) (x2FaceDim s b)
        (X2.x2TrialAll.getD ((x2KeyGlobal s b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize s b) (x2FaceDim s b)
        (X2.x2TrialAll.getD ((x2KeyGlobal s b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ))ᵀ := by
  rw [x2Trial_eq_gram, x2TrialFactor_eq_factorOf]

/-- For an uncorrected key of sector m: the source block in the form. -/
theorem x2SourceM_eq_factorOf (b : x2Key 1) (h : b ∉ x2CorrKeysM) :
    x2SourceM b =
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize 1 b) (x2FaceDim 1 b)
        (X2.x2TrialAll.getD ((x2KeyGlobal 1 b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize 1 b) (x2FaceDim 1 b)
        (X2.x2TrialAll.getD ((x2KeyGlobal 1 b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ))ᵀ := by
  rw [x2SourceM_of_not_mem b h, x2Trial_eq_factorOf]

/-- For an uncorrected key of sector a: the source block in the form. -/
theorem x2SourceA_eq_factorOf (b : x2Key 2) (h : b ∉ x2CorrKeysA) :
    x2SourceA b =
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize 2 b) (x2FaceDim 2 b)
        (X2.x2TrialAll.getD ((x2KeyGlobal 2 b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (X2.x2FactorOf (x2KeySize 2 b) (x2FaceDim 2 b)
        (X2.x2TrialAll.getD ((x2KeyGlobal 2 b : Fin 414) : ℕ) [])).map (Int.cast : ℤ → ℚ))ᵀ := by
  rw [x2SourceA_of_not_mem b h, x2Trial_eq_factorOf]

end ThreeCopyQutritWerner

end
