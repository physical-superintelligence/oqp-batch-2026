module

public import ThreeCopyQutritWerner.Basic
public import ThreeCopyQutritWerner.Continuation
public import ThreeCopyQutritWerner.Product
public import ThreeCopyQutritWerner.Witness
public import ThreeCopyQutritWerner.RankTwo
public import ThreeCopyQutritWerner.RankBridge
public import ThreeCopyQutritWerner.Elementary
public import ThreeCopyQutritWerner.WernerPT
public import ThreeCopyQutritWerner.FamilyI
public import ThreeCopyQutritWerner.Physical
public import ThreeCopyQutritWerner.Distillation
public import ThreeCopyQutritWerner.TwoCutDefs
public import ThreeCopyQutritWerner.TwoCutSOS
public import ThreeCopyQutritWerner.TwoCutIdentity
public import ThreeCopyQutritWerner.TwoCutTransport
public import ThreeCopyQutritWerner.TwoCutRotate
public import ThreeCopyQutritWerner.TwoCutBalanced
public import ThreeCopyQutritWerner.TwoCutFactor
public import ThreeCopyQutritWerner.TwoCutMain
public import ThreeCopyQutritWerner.WernerState
public import ThreeCopyQutritWerner.InteriorReduction
public import ThreeCopyQutritWerner.TwoPlane
public import ThreeCopyQutritWerner.Interior
public import ThreeCopyQutritWerner.InteriorConverse
public import ThreeCopyQutritWerner.Overlap
public import ThreeCopyQutritWerner.RankOne
public import ThreeCopyQutritWerner.Embedding
public import ThreeCopyQutritWerner.OverlapAttain
public import ThreeCopyQutritWerner.Corollaries
public import ThreeCopyQutritWerner.PPTRegion
public import ThreeCopyQutritWerner.Identities
public import ThreeCopyQutritWerner.BinaryZeros
public import ThreeCopyQutritWerner.ZeroFamilies
public import ThreeCopyQutritWerner.QubitEndpoint
public import ThreeCopyQutritWerner.HFeature
public import ThreeCopyQutritWerner.AppendixCInputs
public import ThreeCopyQutritWerner.NoisyFamily
public import ThreeCopyQutritWerner.CertificateReduction
public import ThreeCopyQutritWerner.NoisyFamilyReduction
public import ThreeCopyQutritWerner.ZeroRelations
public import ThreeCopyQutritWerner.TwoQubitPPTCriterion
public import ThreeCopyQutritWerner.AppendixCAssembly
public import ThreeCopyQutritWerner.AppendixCStatementAgreement

@[expose] public section

/-!
# ThreeCopyQutritWerner

The library behind `Solution.lean`. This root imports the modules of the manuscript's analytic results
(Sections 1-3, 5 and 6 and Appendices A-C: the continuation identity, the two-cut and rank-two
inequalities, the Werner-state facts, the PPT region, the zero families of Theorem 5.1, the analytic
inputs of Appendix C, the full-rank family, and the soundness of an exact certificate). The proof of the
endpoint inequality T2.1a from the exact certificate is `ThreeCopyQutritWerner.CertificateX2FinalProof`,
which `Solution.lean` imports together with this root.
-/
