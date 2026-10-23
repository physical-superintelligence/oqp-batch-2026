module

public import ThreeCopyQutritWerner.CertificateX2IntegrationSources
public import ThreeCopyQutritWerner.CertificateX2Data

@[expose] public section


/-!
# T2.1a from the reduced bridge, on the concrete data

The concrete data `x2DataConcrete` (CertificateX2Data), the concrete source blocks `x2SourceM`, `x2SourceA`
(CertificateX2IntegrationSources; their positivity is proved there) and the residual-positivity lemma give
T2.1a from

* `hB : X2ReducedBridge x2DataConcrete` (the bridge's reduced statement for the concrete data), and
* the residual literals: `heq` (residual = literal) and `hpsd` (exact positivity of the literal numerators).

Every fact used is an explicit binder.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The residual blocks of the concrete route-X2 certificate. -/
abbrev x2ResidualConcrete (b : x2Key 0) : Matrix (x2Col 0 b) (x2Col 0 b) ℚ :=
  x2Residual x2DataConcrete x2SourceM x2SourceA b

/-- Residual positivity from literal identities and literal certificates (faces' lemma, concrete). -/
theorem x2ResidualConcrete_posSemidef (den : x2Key 0 → ℤ) (hden : ∀ b, 0 < den b)
    (Nlit : ∀ b : x2Key 0, Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (heq : ∀ b, x2Residual x2DataConcrete x2SourceM x2SourceA b =
      (1 / (den b : ℚ)) • (Nlit b).map (Int.cast : ℤ → ℚ))
    (hpsd : ∀ b, ((Nlit b).map (Int.castRingHom ℂ)).PosSemidef) :
    ∀ b, (x2Complex (x2Residual x2DataConcrete x2SourceM x2SourceA b)).PosSemidef :=
  x2_residualBlocks_posSemidef x2DataConcrete x2SourceM x2SourceA den hden Nlit heq hpsd

/-- CONDITIONAL T2.1a (light form): the reduced bridge for the concrete data, the residual literal
identities and their positivity certificates. Source positivity is discharged
(`x2SourceM_posSemidef`, `x2SourceA_posSemidef`). -/
theorem x2_qutritEndpointInequality_of_reducedBridge (hB : X2ReducedBridge x2DataConcrete)
    (den : x2Key 0 → ℤ) (hden : ∀ b, 0 < den b)
    (Nlit : ∀ b : x2Key 0, Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (heq : ∀ b, x2Residual x2DataConcrete x2SourceM x2SourceA b =
      (1 / (den b : ℚ)) • (Nlit b).map (Int.cast : ℤ → ℚ))
    (hpsd : ∀ b, ((Nlit b).map (Int.castRingHom ℂ)).PosSemidef) :
    QutritEndpointInequality :=
  qutritEndpointInequality_of_x2_reduced x2DataConcrete hB x2SourceM x2SourceA
    x2SourceM_posSemidef x2SourceA_posSemidef
    (x2ResidualConcrete_posSemidef den hden Nlit heq hpsd)

end ThreeCopyQutritWerner

end
