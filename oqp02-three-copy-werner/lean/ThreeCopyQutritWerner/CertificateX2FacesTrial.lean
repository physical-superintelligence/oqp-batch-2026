module

public import ThreeCopyQutritWerner.CertificateX2FacesTrialData
public import ThreeCopyQutritWerner.CertificateX2PackedCore
public import ThreeCopyQutritWerner.CertificateX2PsdReduced

@[expose] public section


/-!
# The trial source blocks (one source of truth)

For every block `b` of
sector `s` (the bridge's `x2Key s`), `x2TrialFactor s b = F = K Z` is the certificate's trial factor in J
coordinates (rows `x2Col s b` = image columns, columns = face dimension), read from the packed data of
CertificateX2FacesTrialData (`X2.ent 80 79` of the packed columns), and

  `x2Trial s b = (1/2^80)² • F Fᵀ`   (the certificate's coefficient block `K Z Zᵀ Kᵀ / 2^160`; zero for empty faces).

Every trial block is positive semidefinite with no data evaluation (`x2Trial_posSemidef`), so a source
family equal to the trial outside the corrected blocks has its `X2ReducedBridge` premise from
`x2_sourceBlocks_posSemidef_of_trial`. The kernel checks that the data have exactly the bridge's row
counts (`x2TrialRows_eq`) and the stated shapes (`X2.x2Trial_shape`).
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The packed row counts are the bridge's image sizes, block by block (kernel check). -/
theorem x2TrialRows_eq : (List.finRange 414).all (fun g =>
    X2.x2TrialRows.getD g 0 == x2GlobalSize g) = true := by
  decide +kernel

/-- Face dimension of block `b` of sector `s` (columns of the certificate's kernel `K`). -/
def x2FaceDim (s : Fin 3) (b : x2Key s) : ℕ := X2.x2TrialDim.getD (x2KeyGlobal s b) 0

/-- The trial factor `F = K Z` of block `b` (J coordinates, scale `2^80`): entry `(i, c)` is slot `i`
of the packed column `c`. -/
def x2TrialFactor (s : Fin 3) (b : x2Key s) : Matrix (x2Col s b) (Fin (x2FaceDim s b)) ℤ :=
  Matrix.of fun i c => X2.ent 80 79 (X2.x2TrialCols (x2KeyGlobal s b) c) i

theorem x2TrialFactor_apply (s : Fin 3) (b : x2Key s) (i : x2Col s b) (c : Fin (x2FaceDim s b)) :
    x2TrialFactor s b i c = X2.ent 80 79 (X2.x2TrialCols (x2KeyGlobal s b) c) i := rfl

/-- THE TRIAL SOURCE BLOCKS: `(1/2^80)² • F Fᵀ` (the certificate's `K Z Zᵀ Kᵀ / 2^160`, J coordinates). -/
def x2Trial (s : Fin 3) : X2Blocks s := fun b =>
  (1 / ((2 ^ 80 : ℤ) : ℚ)) ^ 2 • (x2TrialFactor s b * (x2TrialFactor s b)ᵀ).map (Int.cast : ℤ → ℚ)

theorem x2Trial_apply (s : Fin 3) (b : x2Key s) :
    x2Trial s b = (1 / ((2 ^ 80 : ℤ) : ℚ)) ^ 2 •
      (x2TrialFactor s b * (x2TrialFactor s b)ᵀ).map (Int.cast : ℤ → ℚ) := rfl

/-- Every trial block is positive semidefinite (Gram form; no data evaluation). -/
theorem x2Trial_posSemidef (s : Fin 3) (b : x2Key s) : (x2Complex (x2Trial s b)).PosSemidef := by
  rw [x2Complex_eq_map, x2Trial_apply]
  exact certificateX2_rat_int_gram_posSemidef (x2TrialFactor s b) (2 ^ 80)

/-- SOURCE FAMILIES: equal to the trial outside a set `S` of corrected blocks, whose positivity is
supplied separately (`x2_correctedBlock_posSemidef` with the face-only certificates). -/
theorem x2_sourceBlocks_posSemidef_of_trial {s : Fin 3} (N : X2Blocks s) (S : Set (x2Key s))
    (hN : ∀ b, b ∉ S → N b = x2Trial s b) (hS : ∀ b, b ∈ S → (x2Complex (N b)).PosSemidef) :
    ∀ b, (x2Complex (N b)).PosSemidef := fun b => by
  by_cases h : b ∈ S
  · exact hS b h
  · rw [hN b h]
    exact x2Trial_posSemidef s b

end ThreeCopyQutritWerner

end
