module

public import ThreeCopyQutritWerner.CertificateX2OutFastMeta
public import ThreeCopyQutritWerner.CertificateX2OutLitS2
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2CoreS2gT3
public import ThreeCopyQutritWerner.CertificateX2CoreA2gT3

@[expose] public section


/-! Output stage: `x2Out x2DataConcrete 2 Nsrc b = x2OLit2 b / q` for h block
345-0 from row tables `CoreS2g.t3`, `CoreA2g.t3` (W = 384, slot bound 2^340), by chunk checks (CertificateX2OutFast). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
set_option Elab.async false

namespace ThreeCopyQutritWerner.X2.OutFS2.B345k0
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2


/-- h block `345-0`. -/
def blk : x2Key 0 := ⟨93, by decide⟩

x2_out_jd jd x2J_93 31 750
x2_out_lits C 384 3 4 5 31 CoreS2g.t3 CoreA2g.t3 jd x2J_93

theorem shape : x2KeyMult 0 blk 0 = 5 ∧ x2KeyMult 0 blk 1 = 15 ∧ x2KeyMult 0 blk 2 = 10 ∧
    x2KeySize 0 blk = 31 := by
  decide +kernel

theorem hJ : X2ImageCols x2DataConcrete blk x2J_93 := x2ImageCols_concrete blk

theorem hJc : x2J_93.length = x2KeySize 0 blk := by
  decide +kernel

theorem jd_eq : jd = (List.range (x2KeySize 0 blk)).map fun c =>
    digs 11 (x2KeyMult 0 blk 0 * x2KeyMult 0 blk 1 * x2KeyMult 0 blk 2) (x2J_93.getD c 0) := by
  decide +kernel

theorem c0_0 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 0 (C_L0.getD 0 []) = true := by
  decide +kernel

theorem c0_1 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 1 (C_L0.getD 1 []) = true := by
  decide +kernel

theorem c0_2 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 2 (C_L0.getD 2 []) = true := by
  decide +kernel

theorem c0_3 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 3 (C_L0.getD 3 []) = true := by
  decide +kernel

theorem c0_4 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 4 (C_L0.getD 4 []) = true := by
  decide +kernel

theorem c0_5 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 5 (C_L0.getD 5 []) = true := by
  decide +kernel

theorem c0_6 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 6 (C_L0.getD 6 []) = true := by
  decide +kernel

theorem c0_7 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 7 (C_L0.getD 7 []) = true := by
  decide +kernel

theorem c0_8 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 8 (C_L0.getD 8 []) = true := by
  decide +kernel

theorem c0_9 : x2F0OK 384 340 blk CoreS2g.t3 CoreA2g.t3 jd x2J_93 9 (C_L0.getD 9 []) = true := by
  decide +kernel

theorem c1_0 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 0 (C_L1.getD 0 []) = true := by
  decide +kernel

theorem c1_1 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 1 (C_L1.getD 1 []) = true := by
  decide +kernel

theorem c1_2 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 2 (C_L1.getD 2 []) = true := by
  decide +kernel

theorem c1_3 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 3 (C_L1.getD 3 []) = true := by
  decide +kernel

theorem c1_4 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 4 (C_L1.getD 4 []) = true := by
  decide +kernel

theorem c1_5 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 5 (C_L1.getD 5 []) = true := by
  decide +kernel

theorem c1_6 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 6 (C_L1.getD 6 []) = true := by
  decide +kernel

theorem c1_7 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 7 (C_L1.getD 7 []) = true := by
  decide +kernel

theorem c1_8 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 8 (C_L1.getD 8 []) = true := by
  decide +kernel

theorem c1_9 : x2F1OK 384 340 blk CoreA2g.t3 jd x2J_93 9 (C_L1.getD 9 []) = true := by
  decide +kernel

theorem c2_0 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 0 (C_L2.getD 0 []) = true := by
  decide +kernel

theorem c2_1 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 1 (C_L2.getD 1 []) = true := by
  decide +kernel

theorem c2_2 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 2 (C_L2.getD 2 []) = true := by
  decide +kernel

theorem c2_3 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 3 (C_L2.getD 3 []) = true := by
  decide +kernel

theorem c2_4 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 4 (C_L2.getD 4 []) = true := by
  decide +kernel

theorem c2_5 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 5 (C_L2.getD 5 []) = true := by
  decide +kernel

theorem c2_6 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 6 (C_L2.getD 6 []) = true := by
  decide +kernel

theorem c2_7 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 7 (C_L2.getD 7 []) = true := by
  decide +kernel

theorem c2_8 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 8 (C_L2.getD 8 []) = true := by
  decide +kernel

theorem c2_9 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 9 (C_L2.getD 9 []) = true := by
  decide +kernel

theorem c2_10 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 10 (C_L2.getD 10 []) = true := by
  decide +kernel

theorem c2_11 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 11 (C_L2.getD 11 []) = true := by
  decide +kernel

theorem c2_12 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 12 (C_L2.getD 12 []) = true := by
  decide +kernel

theorem c2_13 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 13 (C_L2.getD 13 []) = true := by
  decide +kernel

theorem c2_14 : x2F2OK 384 340 blk CoreA2g.t3 jd x2J_93 14 (C_L2.getD 14 []) = true := by
  decide +kernel

theorem hsum : (Matrix.of fun (c c' : x2Col 0 blk) =>
    rsum (fun a => ent 384 (384 - 1) ((C_L0.getD a []).getD c' 0) c) (x2KeyMult 0 blk 2) +
      rsum (fun a => ent 384 (384 - 1) ((C_L1.getD a []).getD c' 0) c) (x2KeyMult 0 blk 2) +
      rsum (fun a => ent 384 (384 - 1) ((C_L2.getD a []).getD c' 0) c) (x2KeyMult 0 blk 1)) =
    x2OLit2 blk := by
  decide +kernel

/-- The output of source sector 2 on h block `345-0` from row tables satisfying the global interface. -/
theorem out (Nsrc : X2Blocks 2) (hS : X2TableS x2DataConcrete 2 Nsrc 384 ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) (xfTab CoreS2g.t3))
    (hA : X2TableA x2DataConcrete 2 Nsrc 384 ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) (xfTab CoreA2g.t3)) :
    x2Out x2DataConcrete 2 Nsrc blk =
      Matrix.of fun (c c' : x2Col 0 blk) => ((x2OLit2 blk c c' : ℤ) : ℚ) / ((283890657141096398759152695620634717339097737523396490667600637155361161216000000000 : ℕ) : ℚ) := by
  obtain ⟨h0, h1, h2, hr⟩ := shape
  refine x2Out_of_chunks x2DataConcrete 2 Nsrc blk 384 340 _ CoreS2g.t3 CoreA2g.t3 jd x2J_93 C_L0 C_L1 C_L2 (x2OLit2 blk)
    hJ (x2BlockIface_of_tables _ _ _ blk 384 _ _ _ hS hA) (by norm_num) (by norm_num) hJc
    (xf_jd_ok _ _ _ _ jd_eq) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsum
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · intro a ha
    rw [h2] at ha
    interval_cases a
    · exact c0_0
    · exact c0_1
    · exact c0_2
    · exact c0_3
    · exact c0_4
    · exact c0_5
    · exact c0_6
    · exact c0_7
    · exact c0_8
    · exact c0_9
  · intro a ha
    rw [h2] at ha
    interval_cases a
    · exact c1_0
    · exact c1_1
    · exact c1_2
    · exact c1_3
    · exact c1_4
    · exact c1_5
    · exact c1_6
    · exact c1_7
    · exact c1_8
    · exact c1_9
  · intro a ha
    rw [h1] at ha
    interval_cases a
    · exact c2_0
    · exact c2_1
    · exact c2_2
    · exact c2_3
    · exact c2_4
    · exact c2_5
    · exact c2_6
    · exact c2_7
    · exact c2_8
    · exact c2_9
    · exact c2_10
    · exact c2_11
    · exact c2_12
    · exact c2_13
    · exact c2_14

end ThreeCopyQutritWerner.X2.OutFS2.B345k0
