module

public import ThreeCopyQutritWerner.CertificateX2OutFastMeta
public import ThreeCopyQutritWerner.CertificateX2OutLitS1
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2CoreS1gT3
public import ThreeCopyQutritWerner.CertificateX2CoreA1gT3

@[expose] public section


/-! Output stage: `x2Out x2DataConcrete 1 Nsrc b = x2OLit1 b / q` for h block
455-0 from row tables `CoreS1g.t3`, `CoreA1g.t3` (W = 384, slot bound 2^340), by chunk checks (CertificateX2OutFast). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
set_option Elab.async false

namespace ThreeCopyQutritWerner.X2.OutFS1.B455k0
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2


/-- h block `455-0`. -/
def blk : x2Key 0 := ⟨107, by decide⟩

x2_out_jd jd x2J_107 35 1500
x2_out_lits C 384 4 5 5 35 CoreS1g.t3 CoreA1g.t3 jd x2J_107

theorem shape : x2KeyMult 0 blk 0 = 15 ∧ x2KeyMult 0 blk 1 = 10 ∧ x2KeyMult 0 blk 2 = 10 ∧
    x2KeySize 0 blk = 35 := by
  decide +kernel

theorem hJ : X2ImageCols x2DataConcrete blk x2J_107 := x2ImageCols_concrete blk

theorem hJc : x2J_107.length = x2KeySize 0 blk := by
  decide +kernel

theorem jd_eq : jd = (List.range (x2KeySize 0 blk)).map fun c =>
    digs 11 (x2KeyMult 0 blk 0 * x2KeyMult 0 blk 1 * x2KeyMult 0 blk 2) (x2J_107.getD c 0) := by
  decide +kernel

theorem c0_0 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 0 (C_L0.getD 0 []) = true := by
  decide +kernel

theorem c0_1 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 1 (C_L0.getD 1 []) = true := by
  decide +kernel

theorem c0_2 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 2 (C_L0.getD 2 []) = true := by
  decide +kernel

theorem c0_3 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 3 (C_L0.getD 3 []) = true := by
  decide +kernel

theorem c0_4 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 4 (C_L0.getD 4 []) = true := by
  decide +kernel

theorem c0_5 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 5 (C_L0.getD 5 []) = true := by
  decide +kernel

theorem c0_6 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 6 (C_L0.getD 6 []) = true := by
  decide +kernel

theorem c0_7 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 7 (C_L0.getD 7 []) = true := by
  decide +kernel

theorem c0_8 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 8 (C_L0.getD 8 []) = true := by
  decide +kernel

theorem c0_9 : x2F0OK 384 340 blk CoreS1g.t3 CoreA1g.t3 jd x2J_107 9 (C_L0.getD 9 []) = true := by
  decide +kernel

theorem c1_0 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 0 (C_L1.getD 0 []) = true := by
  decide +kernel

theorem c1_1 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 1 (C_L1.getD 1 []) = true := by
  decide +kernel

theorem c1_2 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 2 (C_L1.getD 2 []) = true := by
  decide +kernel

theorem c1_3 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 3 (C_L1.getD 3 []) = true := by
  decide +kernel

theorem c1_4 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 4 (C_L1.getD 4 []) = true := by
  decide +kernel

theorem c1_5 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 5 (C_L1.getD 5 []) = true := by
  decide +kernel

theorem c1_6 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 6 (C_L1.getD 6 []) = true := by
  decide +kernel

theorem c1_7 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 7 (C_L1.getD 7 []) = true := by
  decide +kernel

theorem c1_8 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 8 (C_L1.getD 8 []) = true := by
  decide +kernel

theorem c1_9 : x2F1OK 384 340 blk CoreA1g.t3 jd x2J_107 9 (C_L1.getD 9 []) = true := by
  decide +kernel

theorem c2_0 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 0 (C_L2.getD 0 []) = true := by
  decide +kernel

theorem c2_1 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 1 (C_L2.getD 1 []) = true := by
  decide +kernel

theorem c2_2 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 2 (C_L2.getD 2 []) = true := by
  decide +kernel

theorem c2_3 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 3 (C_L2.getD 3 []) = true := by
  decide +kernel

theorem c2_4 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 4 (C_L2.getD 4 []) = true := by
  decide +kernel

theorem c2_5 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 5 (C_L2.getD 5 []) = true := by
  decide +kernel

theorem c2_6 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 6 (C_L2.getD 6 []) = true := by
  decide +kernel

theorem c2_7 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 7 (C_L2.getD 7 []) = true := by
  decide +kernel

theorem c2_8 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 8 (C_L2.getD 8 []) = true := by
  decide +kernel

theorem c2_9 : x2F2OK 384 340 blk CoreA1g.t3 jd x2J_107 9 (C_L2.getD 9 []) = true := by
  decide +kernel

theorem hsum : (Matrix.of fun (c c' : x2Col 0 blk) =>
    rsum (fun a => ent 384 (384 - 1) ((C_L0.getD a []).getD c' 0) c) (x2KeyMult 0 blk 2) +
      rsum (fun a => ent 384 (384 - 1) ((C_L1.getD a []).getD c' 0) c) (x2KeyMult 0 blk 2) +
      rsum (fun a => ent 384 (384 - 1) ((C_L2.getD a []).getD c' 0) c) (x2KeyMult 0 blk 1)) =
    x2OLit1 blk := by
  decide +kernel

/-- The output of source sector 1 on h block `455-0` from row tables satisfying the global interface. -/
theorem out (Nsrc : X2Blocks 1) (hS : X2TableS x2DataConcrete 1 Nsrc 384 ((206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 : ℕ) : ℚ) (xfTab CoreS1g.t3))
    (hA : X2TableA x2DataConcrete 1 Nsrc 384 ((206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 : ℕ) : ℚ) (xfTab CoreA1g.t3)) :
    x2Out x2DataConcrete 1 Nsrc blk =
      Matrix.of fun (c c' : x2Col 0 blk) => ((x2OLit1 blk c c' : ℤ) : ℚ) / ((206956289055859274695422315107442708940202250654556041696680864486258286526464000000000 : ℕ) : ℚ) := by
  obtain ⟨h0, h1, h2, hr⟩ := shape
  refine x2Out_of_chunks x2DataConcrete 1 Nsrc blk 384 340 _ CoreS1g.t3 CoreA1g.t3 jd x2J_107 C_L0 C_L1 C_L2 (x2OLit1 blk)
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

end ThreeCopyQutritWerner.X2.OutFS1.B455k0
