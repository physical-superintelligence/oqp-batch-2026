module

public import ThreeCopyQutritWerner.CertificateX2OutFS2All
public import ThreeCopyQutritWerner.CertificateX2CoreS2gTransfer
public import ThreeCopyQutritWerner.CertificateX2CoreA2gTransfer

@[expose] public section


/-! Output stage: the sector-2 output identity on all 122 h blocks, conditional only on
the input-stage hypotheses of the S and A pipelines (their `transfer_global`, hT0 verbatim). -/

set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

namespace ThreeCopyQutritWerner.X2.OutFS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem x2OutputLiteral2_of_hT0 (N : X2Blocks 2)
    (hT0S : ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 2 N i j c =
      (ent 384 (384 - 1) (x2Tab X2.CoreS2g.f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000)
    (hT0A : ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 2 N i j c =
      (ent 384 (384 - 1) (x2Tab X2.CoreA2g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000) :
    ∀ b : x2Key 0, x2Out x2DataConcrete 2 N b =
      Matrix.of fun (c c' : x2Col 0 b) => ((X2.x2OLit2 b c c' : ℤ) : ℚ) / ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) := by
  have hdS : X2.CoreS2g.den = ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) := by unfold X2.CoreS2g.den; norm_num
  have hdA : X2.CoreA2g.den = ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) := by unfold X2.CoreA2g.den; norm_num
  have hS := X2.CoreS2g.transfer_global N hT0S
  have hA := X2.CoreA2g.transfer_global N hT0A
  rw [hdS] at hS
  rw [hdA] at hA
  exact out_all N hS hA

end ThreeCopyQutritWerner.X2.OutFS2
