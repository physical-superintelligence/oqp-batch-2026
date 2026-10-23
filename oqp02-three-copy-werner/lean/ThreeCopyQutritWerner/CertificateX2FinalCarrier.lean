module

public import ThreeCopyQutritWerner.CertificateX2FinalOutputs
public import ThreeCopyQutritWerner.CertificateX2HKeysBridge

@[expose] public section


/-!
# T2.1a from the carrier-fix facts and the two sector output identities

`X2Sites.x2KeyFrameFacts_of_carrierFix` (CertificateX2HKeysBridge) proves every field of
`X2KeyFrameFacts x2DataConcrete` from `carrier_fix`. This module derives T2.1a from the fields of `X2OpenFactsCar`:
* `carrier`: the carrier joint action fixes every h image, `X2CarrierFix`;
* `out1`, `out2` (transfer input stage and output stage): the sector output identities `X2OutputLiteral1/2`.
The carrier fix is proved (`x2CarrierFix_concrete`), so `x2_qutritEndpointInequality_of_outputs` derives T2.1a from
`X2OutputLiteral1` and `X2OutputLiteral2`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The carrier fixes the image of every h block, in frame coordinates. -/
def X2CarrierFix : Prop :=
  ∀ b : x2Key 0, certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame x2DataConcrete b =
    x2ImageFrame x2DataConcrete b

/-- The three facts from which `x2_qutritEndpointInequality_of_openFactsCar` derives T2.1a. -/
structure X2OpenFactsCar : Prop where
  carrier : X2CarrierFix
  out1 : X2OutputLiteral1
  out2 : X2OutputLiteral2

/-- T2.1a from the carrier-fix facts and the two sector output identities (concrete certificate). -/
theorem x2_qutritEndpointInequality_of_openFactsCar (h : X2OpenFactsCar) : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_openFactsOut ⟨X2Sites.x2KeyFrameFacts_of_carrierFix h.carrier, h.out1, h.out2⟩

/-- The carrier-fix facts (`X2Sites.x2KeyFrame_carrier_fix`). -/
theorem x2CarrierFix_concrete : X2CarrierFix := X2Sites.x2KeyFrame_carrier_fix

/-- T2.1a from the two sector output identities (concrete certificate). The other facts used are theorems:
site facts, key frame facts (with the carrier fix), triples, source positivity, positivity of the residual
literals, targets and the residual integer identities. -/
theorem x2_qutritEndpointInequality_of_outputs (h1 : X2OutputLiteral1) (h2 : X2OutputLiteral2) :
    QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_openFactsCar ⟨x2CarrierFix_concrete, h1, h2⟩

end ThreeCopyQutritWerner

end
