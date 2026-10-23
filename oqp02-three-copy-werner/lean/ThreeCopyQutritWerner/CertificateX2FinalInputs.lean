module

public import ThreeCopyQutritWerner.CertificateX2FinalCarrier
public import ThreeCopyQutritWerner.CertificateX2OutFS1Hyp
public import ThreeCopyQutritWerner.CertificateX2OutFS2Hyp
public import ThreeCopyQutritWerner.CertificateX2InputGlueS2

@[expose] public section


/-!
# T2.1a from the three input-stage facts

`x2_qutritEndpointInequality_of_outputs` (CertificateX2FinalCarrier) needs only the two sector output identities
`X2OutputLiteral1/2`. The `X2.OutFS1.x2OutputLiteral1_of_hT0` and `X2.OutFS2.x2OutputLiteral2_of_hT0`
(CertificateX2OutFS1Hyp, CertificateX2OutFS2Hyp) derive them from the input-stage facts of the transfer pipelines
(the `hT0` of their `transfer_global`). For sector 2, pipeline S, that fact is the compiled
`X2.InGS2.hT0` (CertificateX2InputGlueS2, `N = x2SourceA`). The other three are the hypotheses below; their statements are
copied verbatim from the `hT0S`/`hT0A` arguments of the theorems, with `N` instantiated to the concrete
sources `x2SourceM` (sector 1) and `x2SourceA` (sector 2). `CertificateX2FinalProof` supplies them.
-/

noncomputable section

namespace ThreeCopyQutritWerner

open ThreeCopyQutritWerner.X2

/-- Input-stage fact, sector 1, pipeline S, `N = x2SourceM` (the statement of `X2.InGS1.hT0`). -/
def X2InputS1 : Prop :=
  ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 1 x2SourceM i j c =
    (ent 384 (384 - 1) (x2Tab X2.CoreS1g.f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) /
      1108531032609225922165724911675932935547910848716289179910144000

/-- Input-stage fact, sector 1, pipeline A, `N = x2SourceM` (the statement of `X2.InGA1.hT0`). -/
def X2InputA1 : Prop :=
  ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 1 x2SourceM i j c =
    (ent 384 (384 - 1) (x2Tab X2.CoreA1g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) /
      1108531032609225922165724911675932935547910848716289179910144000

/-- Input-stage fact, sector 2, pipeline A, `N = x2SourceA` (the statement of `X2.InGA2.hT0`). -/
def X2InputA2 : Prop :=
  ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 2 x2SourceA i j c =
    (ent 384 (384 - 1) (x2Tab X2.CoreA2g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) /
      1108531032609225922165724911675932935547910848716289179910144000

/-- The sector-1 output identity from the two sector-1 input-stage facts (`X2.OutFS1.x2OutputLiteral1_of_hT0` at `N = x2SourceM`). -/
theorem x2OutputLiteral1_of_inputs (hS1 : X2InputS1) (hA1 : X2InputA1) : X2OutputLiteral1 :=
  X2.OutFS1.x2OutputLiteral1_of_hT0 x2SourceM hS1 hA1

/-- The sector-2 output identity from the sector-2 pipeline-A input-stage fact; pipeline S is the compiled `X2.InGS2.hT0`. -/
theorem x2OutputLiteral2_of_inputs (hA2 : X2InputA2) : X2OutputLiteral2 :=
  X2.OutFS2.x2OutputLiteral2_of_hT0 x2SourceA X2.InGS2.hT0 hA2

/-- T2.1a from the three input-stage facts (concrete certificate). With `X2.InGS1.hT0`, `X2.InGA1.hT0` and
`X2.InGA2.hT0` this is T2.1a (`CertificateX2FinalProof`). -/
theorem x2_qutritEndpointInequality_of_inputs (hS1 : X2InputS1) (hA1 : X2InputA1) (hA2 : X2InputA2) :
    QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_outputs (x2OutputLiteral1_of_inputs hS1 hA1) (x2OutputLiteral2_of_inputs hA2)

end ThreeCopyQutritWerner

end
