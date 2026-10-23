module

public import ThreeCopyQutritWerner.CertificateX2FinalInputs
public import ThreeCopyQutritWerner.CertificateX2InputGlueS1
public import ThreeCopyQutritWerner.CertificateX2InputGlueA1
public import ThreeCopyQutritWerner.CertificateX2InputGlueA2

@[expose] public section


/-!
# T2.1a, `QutritEndpointInequality`

The input-stage theorems `X2.InGS1.hT0`, `X2.InGA1.hT0`, `X2.InGA2.hT0` (N = x2SourceM / x2SourceA;
modules CertificateX2InputGlueS1/A1/A2) have exactly the statements `X2InputS1`, `X2InputA1`, `X2InputA2` that
`x2_qutritEndpointInequality_of_inputs` (CertificateX2FinalInputs) takes; the sector-2 S fact `X2.InGS2.hT0` is used there.
-/

noncomputable section

namespace ThreeCopyQutritWerner

/-- T2.1a (manuscript Theorem 2.1 at `d = 3`, `α = 1/2`): the exact certificate, with its exact correction. -/
theorem x2_qutritEndpointInequality : QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_inputs X2.InGS1.hT0 X2.InGA1.hT0 X2.InGA2.hT0

end ThreeCopyQutritWerner

end
