module

public import ThreeCopyQutritWerner.CertificateX2FacesTrial
public import ThreeCopyQutritWerner.CertificateX2Correction1x006k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x036k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x116k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x346k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x444k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x456k0
public import ThreeCopyQutritWerner.CertificateX2Correction1x555k0
public import ThreeCopyQutritWerner.CertificateX2Correction2x146k0

@[expose] public section


/-!
# The concrete source blocks `x2SourceM`, `x2SourceA`

The source blocks of the certificate in the bridge's reduced statement (`X2Blocks 1`, `X2Blocks 2` of
CertificateX2Reduced): the trial blocks `x2Trial s b` (CertificateX2FacesTrial) outside the eight corrected
blocks, and on the corrected blocks the exact corrected J-coordinate block

  `K_b ((1 / den_X) • A_b) K_bᵀ`,

with `K_b` the block's forced kernel (`X2Correction<n>.K`, rows re-indexed onto the bridge's
`x2Col s b` by `Fin.cast`) and `A_b / den_X` the corrected face block
(`X2Correction<n>Face.A`, `den_X = 2^178 3^9 5^3 7^2`). On these blocks this equals
`x2Trial s b + K_b (Cnum_b / den_c) K_bᵀ` (the `A_eq` with `den_X = den_c`, and
`x2TrialFactor s b = K * Z`; the literals `K`, `Z` of the trial and correction data coincide).

Positivity of every block (`x2SourceM_posSemidef`, `x2SourceA_posSemidef`) uses the trial Gram form and
the exact face certificates `A_psd`; no data is evaluated here.
-/

noncomputable section

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner

/-- Common denominator `den_X = den_c = 2^178 3^9 5^3 7^2` of the corrected face blocks (correction c-v1). -/
def x2CorrDen : ℤ := 46188793025384413423571871319830538981162952029845382496256000

theorem x2CorrDen_pos : 0 < x2CorrDen := by
  unfold x2CorrDen
  norm_num

/-- Replace block `k` of a source family by `M`. -/
def x2PatchBlock {s : Fin 3} (N : X2Blocks s) (k : x2Key s) (M : Matrix (x2Col s k) (x2Col s k) ℚ) :
    X2Blocks s :=
  Function.update N k M

theorem x2PatchBlock_self {s : Fin 3} (N : X2Blocks s) (k : x2Key s)
    (M : Matrix (x2Col s k) (x2Col s k) ℚ) : x2PatchBlock N k M k = M := by
  unfold x2PatchBlock
  first
  | exact Function.update_self (β := fun b : x2Key s => Matrix (x2Col s b) (x2Col s b) ℚ) k M N
  | simp [Function.update]

theorem x2PatchBlock_of_ne {s : Fin 3} (N : X2Blocks s) (k : x2Key s)
    (M : Matrix (x2Col s k) (x2Col s k) ℚ) {b : x2Key s} (h : b ≠ k) : x2PatchBlock N k M b = N b := by
  unfold x2PatchBlock
  first
  | exact Function.update_of_ne (β := fun b : x2Key s => Matrix (x2Col s b) (x2Col s b) ℚ) h M N
  | simp [Function.update, h]

namespace X2Src

/-! ### Corrected block `1-006-0` (`x2Key 1` index 3; image size 3, face dimension 1) -/

/-- The block `1-006-0`. -/
def k1x006k0 : x2Key 1 := ⟨3, by decide⟩

theorem hr1x006k0 : x2KeySize 1 k1x006k0 = 3 := by decide +kernel

/-- The forced kernel `K` of `1-006-0` on the bridge's row index. -/
def K1x006k0 : Matrix (x2Col 1 k1x006k0) (Fin 1) ℤ :=
  Matrix.of fun i j => X2Correction1x006k0.K (Fin.cast hr1x006k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-006-0`. -/
def blk1x006k0 : Matrix (x2Col 1 k1x006k0) (x2Col 1 k1x006k0) ℚ :=
  K1x006k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x006k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x006k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x006k0_posSemidef : (x2Complex blk1x006k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x006k0 X2Correction1x006k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x006k0Face.A_psd

/-! ### Corrected block `1-036-0` (`x2Key 1` index 20; image size 25, face dimension 7) -/

/-- The block `1-036-0`. -/
def k1x036k0 : x2Key 1 := ⟨20, by decide⟩

theorem hr1x036k0 : x2KeySize 1 k1x036k0 = 25 := by decide +kernel

/-- The forced kernel `K` of `1-036-0` on the bridge's row index. -/
def K1x036k0 : Matrix (x2Col 1 k1x036k0) (Fin 7) ℤ :=
  Matrix.of fun i j => X2Correction1x036k0.K (Fin.cast hr1x036k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-036-0`. -/
def blk1x036k0 : Matrix (x2Col 1 k1x036k0) (x2Col 1 k1x036k0) ℚ :=
  K1x036k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x036k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x036k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x036k0_posSemidef : (x2Complex blk1x036k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x036k0 X2Correction1x036k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x036k0Face.A_psd

/-! ### Corrected block `1-116-0` (`x2Key 1` index 44; image size 9, face dimension 2) -/

/-- The block `1-116-0`. -/
def k1x116k0 : x2Key 1 := ⟨44, by decide⟩

theorem hr1x116k0 : x2KeySize 1 k1x116k0 = 9 := by decide +kernel

/-- The forced kernel `K` of `1-116-0` on the bridge's row index. -/
def K1x116k0 : Matrix (x2Col 1 k1x116k0) (Fin 2) ℤ :=
  Matrix.of fun i j => X2Correction1x116k0.K (Fin.cast hr1x116k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-116-0`. -/
def blk1x116k0 : Matrix (x2Col 1 k1x116k0) (x2Col 1 k1x116k0) ℚ :=
  K1x116k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x116k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x116k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x116k0_posSemidef : (x2Complex blk1x116k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x116k0 X2Correction1x116k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x116k0Face.A_psd

/-! ### Corrected block `1-346-0` (`x2Key 1` index 118; image size 179, face dimension 97) -/

/-- The block `1-346-0`. -/
def k1x346k0 : x2Key 1 := ⟨118, by decide⟩

theorem hr1x346k0 : x2KeySize 1 k1x346k0 = 179 := by decide +kernel

/-- The forced kernel `K` of `1-346-0` on the bridge's row index. -/
def K1x346k0 : Matrix (x2Col 1 k1x346k0) (Fin 97) ℤ :=
  Matrix.of fun i j => X2Correction1x346k0.K (Fin.cast hr1x346k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-346-0`. -/
def blk1x346k0 : Matrix (x2Col 1 k1x346k0) (x2Col 1 k1x346k0) ℚ :=
  K1x346k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x346k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x346k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x346k0_posSemidef : (x2Complex blk1x346k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x346k0 X2Correction1x346k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x346k0Face.A_psd

/-! ### Corrected block `1-444-0` (`x2Key 1` index 129; image size 14, face dimension 10) -/

/-- The block `1-444-0`. -/
def k1x444k0 : x2Key 1 := ⟨129, by decide⟩

theorem hr1x444k0 : x2KeySize 1 k1x444k0 = 14 := by decide +kernel

/-- The forced kernel `K` of `1-444-0` on the bridge's row index. -/
def K1x444k0 : Matrix (x2Col 1 k1x444k0) (Fin 10) ℤ :=
  Matrix.of fun i j => X2Correction1x444k0.K (Fin.cast hr1x444k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-444-0`. -/
def blk1x444k0 : Matrix (x2Col 1 k1x444k0) (x2Col 1 k1x444k0) ℚ :=
  K1x444k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x444k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x444k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x444k0_posSemidef : (x2Complex blk1x444k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x444k0 X2Correction1x444k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x444k0Face.A_psd

/-! ### Corrected block `1-456-0` (`x2Key 1` index 140; image size 139, face dimension 98) -/

/-- The block `1-456-0`. -/
def k1x456k0 : x2Key 1 := ⟨140, by decide⟩

theorem hr1x456k0 : x2KeySize 1 k1x456k0 = 139 := by decide +kernel

/-- The forced kernel `K` of `1-456-0` on the bridge's row index. -/
def K1x456k0 : Matrix (x2Col 1 k1x456k0) (Fin 98) ℤ :=
  Matrix.of fun i j => X2Correction1x456k0.K (Fin.cast hr1x456k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-456-0`. -/
def blk1x456k0 : Matrix (x2Col 1 k1x456k0) (x2Col 1 k1x456k0) ℚ :=
  K1x456k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x456k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x456k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x456k0_posSemidef : (x2Complex blk1x456k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x456k0 X2Correction1x456k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x456k0Face.A_psd

/-! ### Corrected block `1-555-0` (`x2Key 1` index 147; image size 11, face dimension 8) -/

/-- The block `1-555-0`. -/
def k1x555k0 : x2Key 1 := ⟨147, by decide⟩

theorem hr1x555k0 : x2KeySize 1 k1x555k0 = 11 := by decide +kernel

/-- The forced kernel `K` of `1-555-0` on the bridge's row index. -/
def K1x555k0 : Matrix (x2Col 1 k1x555k0) (Fin 8) ℤ :=
  Matrix.of fun i j => X2Correction1x555k0.K (Fin.cast hr1x555k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `1-555-0`. -/
def blk1x555k0 : Matrix (x2Col 1 k1x555k0) (x2Col 1 k1x555k0) ℚ :=
  K1x555k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction1x555k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K1x555k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk1x555k0_posSemidef : (x2Complex blk1x555k0).PosSemidef :=
  x2_correctedBlock_posSemidef K1x555k0 X2Correction1x555k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction1x555k0Face.A_psd

/-! ### Corrected block `2-146-0` (`x2Key 2` index 54; image size 55, face dimension 55) -/

/-- The block `2-146-0`. -/
def k2x146k0 : x2Key 2 := ⟨54, by decide⟩

theorem hr2x146k0 : x2KeySize 2 k2x146k0 = 55 := by decide +kernel

/-- The forced kernel `K` of `2-146-0` on the bridge's row index. -/
def K2x146k0 : Matrix (x2Col 2 k2x146k0) (Fin 55) ℤ :=
  Matrix.of fun i j => X2Correction2x146k0.K (Fin.cast hr2x146k0 i) j

/-- The corrected J-coordinate block `K ((1 / den_X) • A) Kᵀ` of `2-146-0`. -/
def blk2x146k0 : Matrix (x2Col 2 k2x146k0) (x2Col 2 k2x146k0) ℚ :=
  K2x146k0.map (Int.cast : ℤ → ℚ) *
    ((1 / ((x2CorrDen : ℤ) : ℚ)) • X2Correction2x146k0Face.A.map (Int.cast : ℤ → ℚ)) *
      (K2x146k0.map (Int.cast : ℤ → ℚ))ᵀ

theorem blk2x146k0_posSemidef : (x2Complex blk2x146k0).PosSemidef :=
  x2_correctedBlock_posSemidef K2x146k0 X2Correction2x146k0Face.A x2CorrDen x2CorrDen_pos
    X2Correction2x146k0Face.A_psd

end X2Src

/-- THE CONCRETE SOURCE BLOCKS of sector m (`s = 1`): the trial outside the corrected blocks
`1-006-0`, `1-036-0`, `1-116-0`, `1-346-0`, `1-444-0`, `1-456-0`, `1-555-0`, the corrected block `K ((1 / den_X) • A) Kᵀ` on them. -/
def x2SourceM : X2Blocks 1 :=
  x2PatchBlock (x2PatchBlock (x2PatchBlock (x2PatchBlock (x2PatchBlock (x2PatchBlock (x2PatchBlock (x2Trial 1) X2Src.k1x006k0 X2Src.blk1x006k0) X2Src.k1x036k0 X2Src.blk1x036k0) X2Src.k1x116k0 X2Src.blk1x116k0) X2Src.k1x346k0 X2Src.blk1x346k0) X2Src.k1x444k0 X2Src.blk1x444k0) X2Src.k1x456k0 X2Src.blk1x456k0) X2Src.k1x555k0 X2Src.blk1x555k0

/-- The corrected blocks of sector m. -/
def x2CorrKeysM : Finset (x2Key 1) := {X2Src.k1x006k0, X2Src.k1x036k0, X2Src.k1x116k0, X2Src.k1x346k0, X2Src.k1x444k0, X2Src.k1x456k0, X2Src.k1x555k0}

theorem x2SourceM_k1x006k0 : x2SourceM X2Src.k1x006k0 = X2Src.blk1x006k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x456k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x444k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x346k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x116k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x006k0 ≠ X2Src.k1x036k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x036k0 : x2SourceM X2Src.k1x036k0 = X2Src.blk1x036k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x036k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x036k0 ≠ X2Src.k1x456k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x036k0 ≠ X2Src.k1x444k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x036k0 ≠ X2Src.k1x346k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x036k0 ≠ X2Src.k1x116k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x116k0 : x2SourceM X2Src.k1x116k0 = X2Src.blk1x116k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x116k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x116k0 ≠ X2Src.k1x456k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x116k0 ≠ X2Src.k1x444k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x116k0 ≠ X2Src.k1x346k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x346k0 : x2SourceM X2Src.k1x346k0 = X2Src.blk1x346k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x346k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x346k0 ≠ X2Src.k1x456k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x346k0 ≠ X2Src.k1x444k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x444k0 : x2SourceM X2Src.k1x444k0 = X2Src.blk1x444k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x444k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_of_ne _ _ _ (show X2Src.k1x444k0 ≠ X2Src.k1x456k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x456k0 : x2SourceM X2Src.k1x456k0 = X2Src.blk1x456k0 := by
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ (show X2Src.k1x456k0 ≠ X2Src.k1x555k0 by decide), x2PatchBlock_self]

theorem x2SourceM_k1x555k0 : x2SourceM X2Src.k1x555k0 = X2Src.blk1x555k0 := by
  rw [x2SourceM, x2PatchBlock_self]

/-- Outside the corrected blocks the source block is the trial block. -/
theorem x2SourceM_of_not_mem (b : x2Key 1) (h : b ∉ x2CorrKeysM) : x2SourceM b = x2Trial 1 b := by
  simp only [x2CorrKeysM, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  rw [x2SourceM, x2PatchBlock_of_ne _ _ _ h6, x2PatchBlock_of_ne _ _ _ h5, x2PatchBlock_of_ne _ _ _ h4, x2PatchBlock_of_ne _ _ _ h3, x2PatchBlock_of_ne _ _ _ h2, x2PatchBlock_of_ne _ _ _ h1, x2PatchBlock_of_ne _ _ _ h0]

/-- Every concrete source block of sector m is positive semidefinite (the `hNm`
premise of `X2ReducedBridge` and of the bridge's `x2_qutritEndpointInequality_of_facts`). -/
theorem x2SourceM_posSemidef : ∀ b, (x2Complex (x2SourceM b)).PosSemidef :=
  x2_sourceBlocks_posSemidef_of_trial x2SourceM (↑x2CorrKeysM)
    (fun b hb => x2SourceM_of_not_mem b hb) (fun b hb => by
    have hb' : b ∈ x2CorrKeysM := hb
    simp only [x2CorrKeysM, Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [x2SourceM_k1x006k0]
      exact X2Src.blk1x006k0_posSemidef
    · rw [x2SourceM_k1x036k0]
      exact X2Src.blk1x036k0_posSemidef
    · rw [x2SourceM_k1x116k0]
      exact X2Src.blk1x116k0_posSemidef
    · rw [x2SourceM_k1x346k0]
      exact X2Src.blk1x346k0_posSemidef
    · rw [x2SourceM_k1x444k0]
      exact X2Src.blk1x444k0_posSemidef
    · rw [x2SourceM_k1x456k0]
      exact X2Src.blk1x456k0_posSemidef
    · rw [x2SourceM_k1x555k0]
      exact X2Src.blk1x555k0_posSemidef)

/-- THE CONCRETE SOURCE BLOCKS of sector a (`s = 2`): the trial outside the corrected blocks
`2-146-0`, the corrected block `K ((1 / den_X) • A) Kᵀ` on them. -/
def x2SourceA : X2Blocks 2 :=
  x2PatchBlock (x2Trial 2) X2Src.k2x146k0 X2Src.blk2x146k0

/-- The corrected blocks of sector a. -/
def x2CorrKeysA : Finset (x2Key 2) := {X2Src.k2x146k0}

theorem x2SourceA_k2x146k0 : x2SourceA X2Src.k2x146k0 = X2Src.blk2x146k0 := by
  rw [x2SourceA, x2PatchBlock_self]

/-- Outside the corrected blocks the source block is the trial block. -/
theorem x2SourceA_of_not_mem (b : x2Key 2) (h : b ∉ x2CorrKeysA) : x2SourceA b = x2Trial 2 b := by
  have h0 : b ≠ X2Src.k2x146k0 := by
    simpa only [x2CorrKeysA, Finset.mem_singleton] using h
  rw [x2SourceA, x2PatchBlock_of_ne _ _ _ h0]

/-- Every concrete source block of sector a is positive semidefinite (the `hNa`
premise of `X2ReducedBridge` and of the bridge's `x2_qutritEndpointInequality_of_facts`). -/
theorem x2SourceA_posSemidef : ∀ b, (x2Complex (x2SourceA b)).PosSemidef :=
  x2_sourceBlocks_posSemidef_of_trial x2SourceA (↑x2CorrKeysA)
    (fun b hb => x2SourceA_of_not_mem b hb) (fun b hb => by
    have hb' : b ∈ x2CorrKeysA := hb
    simp only [x2CorrKeysA, Finset.mem_singleton] at hb'
    subst hb'
    rw [x2SourceA_k2x146k0]
    exact X2Src.blk2x146k0_posSemidef)

end ThreeCopyQutritWerner

end
