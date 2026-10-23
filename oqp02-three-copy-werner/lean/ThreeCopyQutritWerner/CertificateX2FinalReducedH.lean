module

public import ThreeCopyQutritWerner.CertificateX2FinalReduced
public import ThreeCopyQutritWerner.CertificateX2HBlockPsdHFamily

@[expose] public section


/-!
# Residual positivity bound to the literals

The h-block family (CertificateX2HBlockPsdHFamily: `x2HNum`, `x2HNumDen`,
`x2HNum_den_pos`, `x2HNum_psd`; numerators = its literals `X2Nh.nh_<key>` of the corrected residual blocks)
proves the positivity of the residual literals. The residual premise then reduces to the literal identity
`x2Residual x2DataConcrete x2SourceM x2SourceA b = (1 / x2HNumDen b) • x2HNum b`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The residual literal identity: every residual block of the concrete certificate is the literal
`(1 / x2HNumDen b) • x2HNum b`. -/
def X2ResidualLiteral : Prop :=
  ∀ b, x2Residual x2DataConcrete x2SourceM x2SourceA b =
    (1 / (x2HNumDen b : ℚ)) • (x2HNum b).map (Int.cast : ℤ → ℚ)

/-- Residual positivity from the literal identity (with `x2HNum_psd`). -/
theorem x2ResidualConcrete_posSemidef_of_literal (heq : X2ResidualLiteral) :
    ∀ b, (x2Complex (x2Residual x2DataConcrete x2SourceM x2SourceA b)).PosSemidef :=
  x2ResidualConcrete_posSemidef x2HNumDen x2HNum_den_pos x2HNum heq x2HNum_psd

/-- T2.1a from the reduced bridge for the concrete data and the residual literal identity. -/
theorem x2_qutritEndpointInequality_of_reducedBridge_literal (hB : X2ReducedBridge x2DataConcrete)
    (heq : X2ResidualLiteral) : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_reducedBridge hB x2HNumDen x2HNum_den_pos x2HNum heq x2HNum_psd

end ThreeCopyQutritWerner

end
