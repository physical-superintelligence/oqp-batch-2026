module

public import ThreeCopyQutritWerner.CertificateX2FinalCurrent
public import ThreeCopyQutritWerner.CertificateX2OutputResidFaces

@[expose] public section


/-!
# T2.1a from the key frame facts and the two sector output identities

`X2.x2Residual_family_faces` (CertificateX2OutputResidFaces; targets of all 122 h blocks and the
integer combination inside) turns the two sector output identities into the residual literal identity
`X2ResidualLiteral`. This module derives T2.1a from the three fields of `X2OpenFactsOut`:
* `keys`: `X2KeyFrameFacts x2DataConcrete`;
* `out1` (transfer core and output stage): `X2OutputLiteral1`, the sector-1 output on every h block is the
  literal `X2.x2OLit1` over `q1 = 24 den_c den_1^3`;
* `out2`: the same for sector 2, `X2.x2OLit2` over `q2 = 24 den_c den_2^3`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The sector-1 output of the concrete certificate on every h block is the literal `X2.x2OLit1 / q1`. -/
def X2OutputLiteral1 : Prop :=
  ∀ b : x2Key 0, x2Out x2DataConcrete 1 x2SourceM b =
    Matrix.of fun (c c' : x2Col 0 b) => ((X2.x2OLit1 b c c' : ℤ) : ℚ) / ((206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 : ℕ) : ℚ)

/-- The sector-2 output of the concrete certificate on every h block is the literal `X2.x2OLit2 / q2`. -/
def X2OutputLiteral2 : Prop :=
  ∀ b : x2Key 0, x2Out x2DataConcrete 2 x2SourceA b =
    Matrix.of fun (c c' : x2Col 0 b) => ((X2.x2OLit2 b c c' : ℤ) : ℚ) / ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ)

/-- The residual literal identity from the two sector output identities (residual family; targets and
integer identities proved there). -/
theorem x2ResidualLiteral_of_outputs (h1 : X2OutputLiteral1) (h2 : X2OutputLiteral2) : X2ResidualLiteral :=
  X2.x2Residual_family_faces x2SourceM x2SourceA h1 h2

/-- The three facts from which `x2_qutritEndpointInequality_of_openFactsOut` derives T2.1a. -/
structure X2OpenFactsOut : Prop where
  keys : X2KeyFrameFacts x2DataConcrete
  out1 : X2OutputLiteral1
  out2 : X2OutputLiteral2

/-- T2.1a from the key frame facts and the two sector output identities (concrete certificate). -/
theorem x2_qutritEndpointInequality_of_openFactsOut (h : X2OpenFactsOut) : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_keys_residual h.keys (x2ResidualLiteral_of_outputs h.out1 h.out2)

end ThreeCopyQutritWerner

end
