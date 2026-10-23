module

public import ThreeCopyQutritWerner.CertificateX2InputHA2
public import ThreeCopyQutritWerner.CertificateX2IntegrationSourcesFactor

@[expose] public section


/-! HT0 of the A2g pipeline for `N = x2SourceA` exactly (source forms from the concrete sources; corrected keys by entrywise kernel checks of the literals against the packed columns of the input stage). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InGA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem den_eq : ((x2CorrDen : ℤ) : ℚ) = 46188793025384413423571871319830538981162952029845382496256000 := by
  norm_num [x2CorrDen]

theorem K2x146k0_b : (List.finRange (x2KeySize 2 X2Src.k2x146k0)).all (fun i => (List.finRange 55).all (fun j =>
    X2Correction2x146k0.K (Fin.cast X2Src.hr2x146k0 i) j == ent 80 79 (InK2x146.K2x146k0c.getD j 0) i)) = true := by decide +kernel
theorem K2x146k0_entries : ∀ i : Fin (x2KeySize 2 X2Src.k2x146k0), ∀ j : Fin 55,
    X2Correction2x146k0.K (Fin.cast X2Src.hr2x146k0 i) j = ent 80 79 (InK2x146.K2x146k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K2x146k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A2x146k0_b : (List.finRange 55).all (fun c => (List.finRange 55).all (fun d =>
    X2Correction2x146k0Face.A c d == ent 256 (256 - 1) (InK2x146.A2x146k0c.getD d 0) c)) = true := by decide +kernel
theorem A2x146k0_entries : ∀ c d : Fin 55,
    X2Correction2x146k0Face.A c d = ent 256 (256 - 1) (InK2x146.A2x146k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A2x146k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K2x146k0_eq : X2Src.K2x146k0 = x2FactorOf (x2KeySize 2 X2Src.k2x146k0) 55 InK2x146.K2x146k0c := by
  ext i j
  exact K2x146k0_entries i j
theorem A2x146k0_eq : X2Correction2x146k0Face.A = x2AMatOf 55 InK2x146.A2x146k0c := by
  ext c d
  exact A2x146k0_entries c d
theorem corr2x146k0 : x2SourceA ⟨54, by decide⟩ = x2CorrForm 2 ⟨54, by decide⟩ 55 InK2x146.K2x146k0c InK2x146.A2x146k0c := by
  show x2SourceA X2Src.k2x146k0 = _
  rw [x2SourceA_k2x146k0]
  unfold X2Src.blk2x146k0 x2CorrForm
  rw [K2x146k0_eq, A2x146k0_eq, den_eq]
  rfl

/-- The concrete sources of sector 2 in the source forms of the generated input stage. -/
theorem srcForm : InDA2.SrcForm x2SourceA := by
  refine ⟨fun k hk => ?_, corr2x146k0⟩
  have hk' : k ∉ x2CorrKeysA := by
    intro hmem
    apply hk
    simp only [x2CorrKeysA, Finset.mem_insert, Finset.mem_singleton] at hmem
    subst hmem
    decide
  rw [x2SourceA_eq_factorOf k hk']
  rfl

/-- hT0 of `X2.CoreA2g.transfer_unit` and `.transfer_global` for `N = x2SourceA`, verbatim. -/
theorem hT0 : ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 2 x2SourceA i j c =
    (ent 384 (384 - 1) (x2Tab CoreA2g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) /
      1108531032609225922165724911675932935547910848716289179910144000 :=
  InHA2.hT0 x2SourceA x2SourceA_transpose srcForm

end ThreeCopyQutritWerner.X2.InGA2
