module

public import ThreeCopyQutritWerner.CertificateX2Reduced
public import ThreeCopyQutritWerner.CertificateX2PsdRat

@[expose] public section


/-!
# The positivity premises of `X2ReducedBridge`

`X2ReducedBridge D` (CertificateX2Reduced) consumes three
positivity families. This module states them in the bridge's own types and proves them from
data-free hypotheses:

* source blocks (`Nm : X2Blocks 1`, `Na : X2Blocks 2`): every block outside a corrected set is
  the trial Gram form `(1/sc)² • (A Aᵀ)` with an integer factor `A = K Z` (`sc = 2^80`), no data
  check (`x2_sourceBlocks_posSemidef_of_gram`); a corrected block `K M Kᵀ` is positive when its
  face block `M` is (`x2_correctedBlock_posSemidef`; face blocks by the face-only pipeline);
* residual blocks (`x2Residual D Nm Na b`): from the per-block identity
  `x2Residual D Nm Na b = (1/den b) • Nlit b` and the generated per-block certificates
  `X2PsdH0x<key>.psd` (`x2_residualBlocks_posSemidef`).

`qutritEndpointInequality_of_x2_reduced_exact` combines them with `X2ReducedBridge D`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- `x2Complex` is the cast used throughout CertificateX2PsdRat. -/
theorem x2Complex_eq_map {n : Type*} (M : Matrix n n ℚ) :
    x2Complex M = M.map (fun q : ℚ => (q : ℂ)) := rfl

/-- SOURCE BLOCKS: trial Gram blocks `(1/sc b)² • (A b)(A b)ᵀ` outside a set `S` of corrected
blocks (empty faces: `A b` with no columns, i.e. the zero block). -/
theorem x2_sourceBlocks_posSemidef_of_gram {s : Fin 3} (N : X2Blocks s) (S : Set (x2Key s))
    {e : x2Key s → Type*} [∀ b, Fintype (e b)] (A : ∀ b, Matrix (x2Col s b) (e b) ℤ)
    (sc : x2Key s → ℤ)
    (hN : ∀ b, b ∉ S → N b = (1 / (sc b : ℚ)) ^ 2 • (A b * (A b)ᵀ).map (Int.cast : ℤ → ℚ))
    (hS : ∀ b, b ∈ S → (x2Complex (N b)).PosSemidef) :
    ∀ b, (x2Complex (N b)).PosSemidef := by
  intro b
  rw [x2Complex_eq_map]
  exact certificateX2_rat_int_blocks_posSemidef_of_gram_except S N A sc hN
    (fun b hb => by rw [← x2Complex_eq_map]; exact hS b hb) b

/-- CORRECTED SOURCE BLOCKS: `K ((1/den) • A) Kᵀ` is positive when the integer face block `A` is
(`A = den · (Z Zᵀ / 2^160 + C_b)`, the convention). -/
theorem x2_correctedBlock_posSemidef {r n : Type*} [Fintype r] [Fintype n]
    (K : Matrix r n ℤ) (A : Matrix n n ℤ) (den : ℤ) (hden : 0 < den)
    (hA : (A.map (Int.castRingHom ℂ)).PosSemidef) :
    (x2Complex (K.map (Int.cast : ℤ → ℚ) * ((1 / (den : ℚ)) • A.map (Int.cast : ℤ → ℚ)) *
      (K.map (Int.cast : ℤ → ℚ))ᵀ)).PosSemidef := by
  rw [x2Complex_eq_map]
  exact certificateX2_rat_congr_posSemidef _ _ (certificateX2_rat_int_div_posSemidef A den hden hA)

/-- RESIDUAL BLOCKS: per-block literal identities and per-block exact positivity of the integer
numerators give the residual family of `X2ReducedBridge`. -/
theorem x2_residualBlocks_posSemidef (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (den : x2Key 0 → ℤ) (hden : ∀ b, 0 < den b)
    (Nlit : ∀ b : x2Key 0, Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (heq : ∀ b, x2Residual D Nm Na b = (1 / (den b : ℚ)) • (Nlit b).map (Int.cast : ℤ → ℚ))
    (hpsd : ∀ b, ((Nlit b).map (Int.castRingHom ℂ)).PosSemidef) :
    ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef := by
  intro b
  rw [heq b, x2Complex_eq_map]
  exact certificateX2_rat_int_div_posSemidef (Nlit b) (den b) (hden b) (hpsd b)

/-- The reduced bridge and the three positivity families prove T2.1a. -/
theorem qutritEndpointInequality_of_x2_reduced (D : X2Data) (hB : X2ReducedBridge D)
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ b, (x2Complex (Nm b)).PosSemidef) (hNa : ∀ b, (x2Complex (Na b)).PosSemidef)
    (hNh : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) : QutritEndpointInequality :=
  hB Nm Na hNm hNa hNh

/-- ROUTE X2, POSITIVITY SIDE COMPLETE: the reduced bridge, trial Gram blocks outside the
corrected sets, separately checked corrected blocks, and exact residual literals with their
per-block certificates prove T2.1a. No margin, perturbation bound or spectral premise. -/
theorem qutritEndpointInequality_of_x2_reduced_exact (D : X2Data) (hB : X2ReducedBridge D)
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (Sm : Set (x2Key 1)) {em : x2Key 1 → Type*} [∀ b, Fintype (em b)]
    (Am : ∀ b, Matrix (x2Col 1 b) (em b) ℤ) (scm : x2Key 1 → ℤ)
    (hNm : ∀ b, b ∉ Sm → Nm b = (1 / (scm b : ℚ)) ^ 2 • (Am b * (Am b)ᵀ).map (Int.cast : ℤ → ℚ))
    (hSm : ∀ b, b ∈ Sm → (x2Complex (Nm b)).PosSemidef)
    (Sa : Set (x2Key 2)) {ea : x2Key 2 → Type*} [∀ b, Fintype (ea b)]
    (Aa : ∀ b, Matrix (x2Col 2 b) (ea b) ℤ) (sca : x2Key 2 → ℤ)
    (hNa : ∀ b, b ∉ Sa → Na b = (1 / (sca b : ℚ)) ^ 2 • (Aa b * (Aa b)ᵀ).map (Int.cast : ℤ → ℚ))
    (hSa : ∀ b, b ∈ Sa → (x2Complex (Na b)).PosSemidef)
    (den : x2Key 0 → ℤ) (hden : ∀ b, 0 < den b)
    (Nlit : ∀ b : x2Key 0, Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (heq : ∀ b, x2Residual D Nm Na b = (1 / (den b : ℚ)) • (Nlit b).map (Int.cast : ℤ → ℚ))
    (hpsd : ∀ b, ((Nlit b).map (Int.castRingHom ℂ)).PosSemidef) : QutritEndpointInequality :=
  hB Nm Na (x2_sourceBlocks_posSemidef_of_gram Nm Sm Am scm hNm hSm)
    (x2_sourceBlocks_posSemidef_of_gram Na Sa Aa sca hNa hSa)
    (x2_residualBlocks_posSemidef D Nm Na den hden Nlit heq hpsd)

end ThreeCopyQutritWerner

end
