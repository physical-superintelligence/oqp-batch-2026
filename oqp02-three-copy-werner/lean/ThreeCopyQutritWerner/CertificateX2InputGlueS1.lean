module

public import ThreeCopyQutritWerner.CertificateX2InputHS1
public import ThreeCopyQutritWerner.CertificateX2IntegrationSourcesFactor

@[expose] public section


/-! HT0 of the S1g pipeline for `N = x2SourceM` exactly (source forms from the concrete sources; corrected keys by entrywise kernel checks of the literals against the packed columns of the input stage). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InGS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem den_eq : ((x2CorrDen : ℤ) : ℚ) = 46188793025384413423571871319830538981162952029845382496256000 := by
  norm_num [x2CorrDen]

theorem K1x006k0_b : (List.finRange (x2KeySize 1 X2Src.k1x006k0)).all (fun i => (List.finRange 1).all (fun j =>
    X2Correction1x006k0.K (Fin.cast X2Src.hr1x006k0 i) j == ent 80 79 (InK1x006.K1x006k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x006k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x006k0), ∀ j : Fin 1,
    X2Correction1x006k0.K (Fin.cast X2Src.hr1x006k0 i) j = ent 80 79 (InK1x006.K1x006k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x006k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x006k0_b : (List.finRange 1).all (fun c => (List.finRange 1).all (fun d =>
    X2Correction1x006k0Face.A c d == ent 256 (256 - 1) (InK1x006.A1x006k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x006k0_entries : ∀ c d : Fin 1,
    X2Correction1x006k0Face.A c d = ent 256 (256 - 1) (InK1x006.A1x006k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x006k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x006k0_eq : X2Src.K1x006k0 = x2FactorOf (x2KeySize 1 X2Src.k1x006k0) 1 InK1x006.K1x006k0c := by
  ext i j
  exact K1x006k0_entries i j
theorem A1x006k0_eq : X2Correction1x006k0Face.A = x2AMatOf 1 InK1x006.A1x006k0c := by
  ext c d
  exact A1x006k0_entries c d
theorem corr1x006k0 : x2SourceM ⟨3, by decide⟩ = x2CorrForm 1 ⟨3, by decide⟩ 1 InK1x006.K1x006k0c InK1x006.A1x006k0c := by
  show x2SourceM X2Src.k1x006k0 = _
  rw [x2SourceM_k1x006k0]
  unfold X2Src.blk1x006k0 x2CorrForm
  rw [K1x006k0_eq, A1x006k0_eq, den_eq]
  rfl

theorem K1x036k0_b : (List.finRange (x2KeySize 1 X2Src.k1x036k0)).all (fun i => (List.finRange 7).all (fun j =>
    X2Correction1x036k0.K (Fin.cast X2Src.hr1x036k0 i) j == ent 80 79 (InK1x036.K1x036k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x036k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x036k0), ∀ j : Fin 7,
    X2Correction1x036k0.K (Fin.cast X2Src.hr1x036k0 i) j = ent 80 79 (InK1x036.K1x036k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x036k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x036k0_b : (List.finRange 7).all (fun c => (List.finRange 7).all (fun d =>
    X2Correction1x036k0Face.A c d == ent 256 (256 - 1) (InK1x036.A1x036k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x036k0_entries : ∀ c d : Fin 7,
    X2Correction1x036k0Face.A c d = ent 256 (256 - 1) (InK1x036.A1x036k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x036k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x036k0_eq : X2Src.K1x036k0 = x2FactorOf (x2KeySize 1 X2Src.k1x036k0) 7 InK1x036.K1x036k0c := by
  ext i j
  exact K1x036k0_entries i j
theorem A1x036k0_eq : X2Correction1x036k0Face.A = x2AMatOf 7 InK1x036.A1x036k0c := by
  ext c d
  exact A1x036k0_entries c d
theorem corr1x036k0 : x2SourceM ⟨20, by decide⟩ = x2CorrForm 1 ⟨20, by decide⟩ 7 InK1x036.K1x036k0c InK1x036.A1x036k0c := by
  show x2SourceM X2Src.k1x036k0 = _
  rw [x2SourceM_k1x036k0]
  unfold X2Src.blk1x036k0 x2CorrForm
  rw [K1x036k0_eq, A1x036k0_eq, den_eq]
  rfl

theorem K1x116k0_b : (List.finRange (x2KeySize 1 X2Src.k1x116k0)).all (fun i => (List.finRange 2).all (fun j =>
    X2Correction1x116k0.K (Fin.cast X2Src.hr1x116k0 i) j == ent 80 79 (InK1x116.K1x116k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x116k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x116k0), ∀ j : Fin 2,
    X2Correction1x116k0.K (Fin.cast X2Src.hr1x116k0 i) j = ent 80 79 (InK1x116.K1x116k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x116k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x116k0_b : (List.finRange 2).all (fun c => (List.finRange 2).all (fun d =>
    X2Correction1x116k0Face.A c d == ent 256 (256 - 1) (InK1x116.A1x116k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x116k0_entries : ∀ c d : Fin 2,
    X2Correction1x116k0Face.A c d = ent 256 (256 - 1) (InK1x116.A1x116k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x116k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x116k0_eq : X2Src.K1x116k0 = x2FactorOf (x2KeySize 1 X2Src.k1x116k0) 2 InK1x116.K1x116k0c := by
  ext i j
  exact K1x116k0_entries i j
theorem A1x116k0_eq : X2Correction1x116k0Face.A = x2AMatOf 2 InK1x116.A1x116k0c := by
  ext c d
  exact A1x116k0_entries c d
theorem corr1x116k0 : x2SourceM ⟨44, by decide⟩ = x2CorrForm 1 ⟨44, by decide⟩ 2 InK1x116.K1x116k0c InK1x116.A1x116k0c := by
  show x2SourceM X2Src.k1x116k0 = _
  rw [x2SourceM_k1x116k0]
  unfold X2Src.blk1x116k0 x2CorrForm
  rw [K1x116k0_eq, A1x116k0_eq, den_eq]
  rfl

theorem K1x346k0_b : (List.finRange (x2KeySize 1 X2Src.k1x346k0)).all (fun i => (List.finRange 97).all (fun j =>
    X2Correction1x346k0.K (Fin.cast X2Src.hr1x346k0 i) j == ent 80 79 (InK1x346.K1x346k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x346k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x346k0), ∀ j : Fin 97,
    X2Correction1x346k0.K (Fin.cast X2Src.hr1x346k0 i) j = ent 80 79 (InK1x346.K1x346k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x346k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x346k0_b : (List.finRange 97).all (fun c => (List.finRange 97).all (fun d =>
    X2Correction1x346k0Face.A c d == ent 256 (256 - 1) (InK1x346.A1x346k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x346k0_entries : ∀ c d : Fin 97,
    X2Correction1x346k0Face.A c d = ent 256 (256 - 1) (InK1x346.A1x346k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x346k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x346k0_eq : X2Src.K1x346k0 = x2FactorOf (x2KeySize 1 X2Src.k1x346k0) 97 InK1x346.K1x346k0c := by
  ext i j
  exact K1x346k0_entries i j
theorem A1x346k0_eq : X2Correction1x346k0Face.A = x2AMatOf 97 InK1x346.A1x346k0c := by
  ext c d
  exact A1x346k0_entries c d
theorem corr1x346k0 : x2SourceM ⟨118, by decide⟩ = x2CorrForm 1 ⟨118, by decide⟩ 97 InK1x346.K1x346k0c InK1x346.A1x346k0c := by
  show x2SourceM X2Src.k1x346k0 = _
  rw [x2SourceM_k1x346k0]
  unfold X2Src.blk1x346k0 x2CorrForm
  rw [K1x346k0_eq, A1x346k0_eq, den_eq]
  rfl

theorem K1x444k0_b : (List.finRange (x2KeySize 1 X2Src.k1x444k0)).all (fun i => (List.finRange 10).all (fun j =>
    X2Correction1x444k0.K (Fin.cast X2Src.hr1x444k0 i) j == ent 80 79 (InK1x444.K1x444k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x444k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x444k0), ∀ j : Fin 10,
    X2Correction1x444k0.K (Fin.cast X2Src.hr1x444k0 i) j = ent 80 79 (InK1x444.K1x444k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x444k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x444k0_b : (List.finRange 10).all (fun c => (List.finRange 10).all (fun d =>
    X2Correction1x444k0Face.A c d == ent 256 (256 - 1) (InK1x444.A1x444k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x444k0_entries : ∀ c d : Fin 10,
    X2Correction1x444k0Face.A c d = ent 256 (256 - 1) (InK1x444.A1x444k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x444k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x444k0_eq : X2Src.K1x444k0 = x2FactorOf (x2KeySize 1 X2Src.k1x444k0) 10 InK1x444.K1x444k0c := by
  ext i j
  exact K1x444k0_entries i j
theorem A1x444k0_eq : X2Correction1x444k0Face.A = x2AMatOf 10 InK1x444.A1x444k0c := by
  ext c d
  exact A1x444k0_entries c d
theorem corr1x444k0 : x2SourceM ⟨129, by decide⟩ = x2CorrForm 1 ⟨129, by decide⟩ 10 InK1x444.K1x444k0c InK1x444.A1x444k0c := by
  show x2SourceM X2Src.k1x444k0 = _
  rw [x2SourceM_k1x444k0]
  unfold X2Src.blk1x444k0 x2CorrForm
  rw [K1x444k0_eq, A1x444k0_eq, den_eq]
  rfl

theorem K1x456k0_b : (List.finRange (x2KeySize 1 X2Src.k1x456k0)).all (fun i => (List.finRange 98).all (fun j =>
    X2Correction1x456k0.K (Fin.cast X2Src.hr1x456k0 i) j == ent 80 79 (InK1x456.K1x456k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x456k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x456k0), ∀ j : Fin 98,
    X2Correction1x456k0.K (Fin.cast X2Src.hr1x456k0 i) j = ent 80 79 (InK1x456.K1x456k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x456k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x456k0_b : (List.finRange 98).all (fun c => (List.finRange 98).all (fun d =>
    X2Correction1x456k0Face.A c d == ent 256 (256 - 1) (InK1x456.A1x456k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x456k0_entries : ∀ c d : Fin 98,
    X2Correction1x456k0Face.A c d = ent 256 (256 - 1) (InK1x456.A1x456k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x456k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x456k0_eq : X2Src.K1x456k0 = x2FactorOf (x2KeySize 1 X2Src.k1x456k0) 98 InK1x456.K1x456k0c := by
  ext i j
  exact K1x456k0_entries i j
theorem A1x456k0_eq : X2Correction1x456k0Face.A = x2AMatOf 98 InK1x456.A1x456k0c := by
  ext c d
  exact A1x456k0_entries c d
theorem corr1x456k0 : x2SourceM ⟨140, by decide⟩ = x2CorrForm 1 ⟨140, by decide⟩ 98 InK1x456.K1x456k0c InK1x456.A1x456k0c := by
  show x2SourceM X2Src.k1x456k0 = _
  rw [x2SourceM_k1x456k0]
  unfold X2Src.blk1x456k0 x2CorrForm
  rw [K1x456k0_eq, A1x456k0_eq, den_eq]
  rfl

theorem K1x555k0_b : (List.finRange (x2KeySize 1 X2Src.k1x555k0)).all (fun i => (List.finRange 8).all (fun j =>
    X2Correction1x555k0.K (Fin.cast X2Src.hr1x555k0 i) j == ent 80 79 (InK1x555.K1x555k0c.getD j 0) i)) = true := by decide +kernel
theorem K1x555k0_entries : ∀ i : Fin (x2KeySize 1 X2Src.k1x555k0), ∀ j : Fin 8,
    X2Correction1x555k0.K (Fin.cast X2Src.hr1x555k0 i) j = ent 80 79 (InK1x555.K1x555k0c.getD j 0) i :=
  fun i j => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp K1x555k0_b i (List.mem_finRange i)) j (List.mem_finRange j))
theorem A1x555k0_b : (List.finRange 8).all (fun c => (List.finRange 8).all (fun d =>
    X2Correction1x555k0Face.A c d == ent 256 (256 - 1) (InK1x555.A1x555k0c.getD d 0) c)) = true := by decide +kernel
theorem A1x555k0_entries : ∀ c d : Fin 8,
    X2Correction1x555k0Face.A c d = ent 256 (256 - 1) (InK1x555.A1x555k0c.getD d 0) c :=
  fun c d => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp A1x555k0_b c (List.mem_finRange c)) d (List.mem_finRange d))
theorem K1x555k0_eq : X2Src.K1x555k0 = x2FactorOf (x2KeySize 1 X2Src.k1x555k0) 8 InK1x555.K1x555k0c := by
  ext i j
  exact K1x555k0_entries i j
theorem A1x555k0_eq : X2Correction1x555k0Face.A = x2AMatOf 8 InK1x555.A1x555k0c := by
  ext c d
  exact A1x555k0_entries c d
theorem corr1x555k0 : x2SourceM ⟨147, by decide⟩ = x2CorrForm 1 ⟨147, by decide⟩ 8 InK1x555.K1x555k0c InK1x555.A1x555k0c := by
  show x2SourceM X2Src.k1x555k0 = _
  rw [x2SourceM_k1x555k0]
  unfold X2Src.blk1x555k0 x2CorrForm
  rw [K1x555k0_eq, A1x555k0_eq, den_eq]
  rfl

/-- The concrete sources of sector 1 in the source forms of the generated input stage. -/
theorem srcForm : InDS1.SrcForm x2SourceM := by
  refine ⟨fun k hk => ?_, corr1x006k0, corr1x036k0, corr1x116k0, corr1x346k0, corr1x444k0, corr1x456k0, corr1x555k0⟩
  have hk' : k ∉ x2CorrKeysM := by
    intro hmem
    apply hk
    simp only [x2CorrKeysM, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [x2SourceM_eq_factorOf k hk']
  rfl

/-- hT0 of `X2.CoreS1g.transfer_unit` and `.transfer_global` for `N = x2SourceM`, verbatim. -/
theorem hT0 : ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 1 x2SourceM i j c =
    (ent 384 (384 - 1) (x2Tab CoreS1g.f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) /
      1108531032609225922165724911675932935547910848716289179910144000 :=
  InHS1.hT0 x2SourceM x2SourceM_transpose srcForm

end ThreeCopyQutritWerner.X2.InGS1
