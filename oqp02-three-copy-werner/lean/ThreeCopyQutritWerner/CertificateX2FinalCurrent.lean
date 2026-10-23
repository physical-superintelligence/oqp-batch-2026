module

public import ThreeCopyQutritWerner.CertificateX2BridgeTriple
public import ThreeCopyQutritWerner.CertificateX2SitesBridge
public import ThreeCopyQutritWerner.CertificateX2FinalReducedH

@[expose] public section


/-!
# T2.1a from the per-key frame facts and the residual literal identity

Combines, for the concrete certificate (`x2DataConcrete`, `x2SourceM`, `x2SourceA`):
* `x2_qutritEndpointInequality_of_facts'` (CertificateX2BridgeTriple, which also handles the triples of three
  equal types);
* `X2Sites.x2SiteFacts_of_trans` with the explicit unit weights `X2Sites.x2SitesW`;
* positivity of the source blocks (CertificateX2IntegrationSources) and of the residual literals (`x2HNum_psd`).

The theorems below derive T2.1a from the two fields of `X2OpenFactsNow`: the per-key frame facts
`X2KeyFrameFacts x2DataConcrete` and the residual literal identity `X2ResidualLiteral`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The two facts from which `x2_qutritEndpointInequality_of_openFactsNow` derives T2.1a. -/
structure X2OpenFactsNow : Prop where
  keys : X2KeyFrameFacts x2DataConcrete
  residual : X2ResidualLiteral

/-- T2.1a from the per-key frame facts and the residual literal identity (concrete certificate). -/
theorem x2_qutritEndpointInequality_of_keys_residual (hK : X2KeyFrameFacts x2DataConcrete)
    (heq : X2ResidualLiteral) : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_facts' x2DataConcrete (X2Sites.x2SitesW 1) (X2Sites.x2SitesW 2)
    (X2Sites.x2SiteFacts_of_trans x2DataConcrete rfl rfl) hK x2SourceM x2SourceA
    x2SourceM_posSemidef x2SourceA_posSemidef (x2ResidualConcrete_posSemidef_of_literal heq)

/-- The bridge's reduced statement for the concrete data, from the per-key frame facts alone (the site
facts and the triples of three equal types are proved). -/
theorem x2ReducedBridge_concrete_of_keys (hK : X2KeyFrameFacts x2DataConcrete) :
    X2ReducedBridge x2DataConcrete :=
  fun Nm Na hNm hNa hres =>
    x2_qutritEndpointInequality_of_facts' x2DataConcrete (X2Sites.x2SitesW 1) (X2Sites.x2SitesW 2)
      (X2Sites.x2SiteFacts_of_trans x2DataConcrete rfl rfl) hK Nm Na hNm hNa hres

/-- The same, from the structure `X2OpenFactsNow`. -/
theorem x2_qutritEndpointInequality_of_openFactsNow (h : X2OpenFactsNow) : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_keys_residual h.keys h.residual

end ThreeCopyQutritWerner

end
