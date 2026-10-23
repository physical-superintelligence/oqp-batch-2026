module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [35, 40). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col35_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 0 v) = true := by decide +kernel
theorem col35_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 1 v) = true := by decide +kernel
theorem s35_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 0 = true := by decide +kernel
theorem s35_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 1 = true := by decide +kernel
theorem s35_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 2 = true := by decide +kernel
theorem s35_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 3 = true := by decide +kernel
theorem k35_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k35_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k35_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s35_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k35_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k35_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k35_2_4_80 k h.1 (by omega)
theorem s35_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 5 = true := by decide +kernel
theorem s35_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 6 = true := by decide +kernel
theorem s35_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 2 7 = true := by decide +kernel
theorem s35_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 0 = true := by decide +kernel
theorem s35_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 1 = true := by decide +kernel
theorem s35_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 2 = true := by decide +kernel
theorem s35_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 3 = true := by decide +kernel
theorem k35_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k35_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k35_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s35_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k35_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k35_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 35) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (35 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k35_3_4_80 k h.1 (by omega)
theorem s35_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 5 = true := by decide +kernel
theorem s35_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 6 = true := by decide +kernel
theorem s35_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 3 7 = true := by decide +kernel
theorem s35_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 0 = true := by decide +kernel
theorem s35_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 1 = true := by decide +kernel
theorem s35_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 2 = true := by decide +kernel
theorem s35_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 3 = true := by decide +kernel
theorem s35_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 4 = true := by decide +kernel
theorem k35_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k35_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k35_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k35_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k35_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k35_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k35_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k35_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k35_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s35_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k35_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k35_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k35_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k35_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k35_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k35_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k35_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k35_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 5).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k35_4_5_40 k h.1 (by omega)
theorem k35_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k35_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k35_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k35_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k35_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k35_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k35_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k35_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k35_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k35_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k35_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s35_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k35_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k35_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k35_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k35_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k35_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k35_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k35_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k35_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k35_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k35_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 4 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k35_4_6_50 k h.1 (by omega)
theorem s35_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 4 7 = true := by decide +kernel
theorem s35_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 0 = true := by decide +kernel
theorem s35_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 1 = true := by decide +kernel
theorem s35_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 2 = true := by decide +kernel
theorem s35_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 3 = true := by decide +kernel
theorem s35_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 4 = true := by decide +kernel
theorem s35_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 5 = true := by decide +kernel
theorem k35_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k35_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k35_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k35_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k35_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k35_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s35_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k35_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k35_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k35_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k35_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k35_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 35) ((InDA2.TCasaD 4 5 6).getD (35 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k35_5_6_50 k h.1 (by omega)
theorem s35_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 5 7 = true := by decide +kernel
theorem col35_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 6 v) = true := by decide +kernel
theorem col35_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 7 v) = true := by decide +kernel
theorem col35 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 35) 35 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col35_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col35_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s35_2_0
    · exact s35_2_1
    · exact s35_2_2
    · exact s35_2_3
    · exact s35_2_4
    · exact s35_2_5
    · exact s35_2_6
    · exact s35_2_7
  · fin_cases v
    · exact s35_3_0
    · exact s35_3_1
    · exact s35_3_2
    · exact s35_3_3
    · exact s35_3_4
    · exact s35_3_5
    · exact s35_3_6
    · exact s35_3_7
  · fin_cases v
    · exact s35_4_0
    · exact s35_4_1
    · exact s35_4_2
    · exact s35_4_3
    · exact s35_4_4
    · exact s35_4_5
    · exact s35_4_6
    · exact s35_4_7
  · fin_cases v
    · exact s35_5_0
    · exact s35_5_1
    · exact s35_5_2
    · exact s35_5_3
    · exact s35_5_4
    · exact s35_5_5
    · exact s35_5_6
    · exact s35_5_7
  · exact List.all_eq_true.mp col35_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col35_7 v (List.mem_finRange v)
theorem col36_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 0 v) = true := by decide +kernel
theorem col36_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 1 v) = true := by decide +kernel
theorem s36_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 0 = true := by decide +kernel
theorem s36_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 1 = true := by decide +kernel
theorem s36_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 2 = true := by decide +kernel
theorem s36_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 3 = true := by decide +kernel
theorem k36_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k36_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k36_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s36_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k36_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k36_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k36_2_4_80 k h.1 (by omega)
theorem s36_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 5 = true := by decide +kernel
theorem s36_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 6 = true := by decide +kernel
theorem s36_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 2 7 = true := by decide +kernel
theorem s36_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 0 = true := by decide +kernel
theorem s36_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 1 = true := by decide +kernel
theorem s36_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 2 = true := by decide +kernel
theorem s36_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 3 = true := by decide +kernel
theorem k36_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k36_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k36_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s36_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k36_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k36_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 36) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (36 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k36_3_4_80 k h.1 (by omega)
theorem s36_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 5 = true := by decide +kernel
theorem s36_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 6 = true := by decide +kernel
theorem s36_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 3 7 = true := by decide +kernel
theorem s36_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 0 = true := by decide +kernel
theorem s36_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 1 = true := by decide +kernel
theorem s36_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 2 = true := by decide +kernel
theorem s36_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 3 = true := by decide +kernel
theorem s36_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 4 = true := by decide +kernel
theorem k36_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k36_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k36_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k36_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k36_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k36_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k36_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k36_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k36_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s36_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k36_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k36_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k36_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k36_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k36_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k36_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k36_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k36_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 5).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k36_4_5_40 k h.1 (by omega)
theorem k36_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k36_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k36_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k36_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k36_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k36_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k36_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k36_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k36_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k36_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k36_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s36_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k36_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k36_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k36_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k36_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k36_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k36_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k36_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k36_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k36_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k36_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 4 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k36_4_6_50 k h.1 (by omega)
theorem s36_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 4 7 = true := by decide +kernel
theorem s36_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 0 = true := by decide +kernel
theorem s36_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 1 = true := by decide +kernel
theorem s36_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 2 = true := by decide +kernel
theorem s36_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 3 = true := by decide +kernel
theorem s36_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 4 = true := by decide +kernel
theorem s36_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 5 = true := by decide +kernel
theorem k36_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k36_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k36_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k36_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k36_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k36_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s36_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k36_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k36_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k36_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k36_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k36_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 36) ((InDA2.TCasaD 4 5 6).getD (36 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k36_5_6_50 k h.1 (by omega)
theorem s36_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 5 7 = true := by decide +kernel
theorem col36_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 6 v) = true := by decide +kernel
theorem col36_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 7 v) = true := by decide +kernel
theorem col36 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 36) 36 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col36_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col36_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s36_2_0
    · exact s36_2_1
    · exact s36_2_2
    · exact s36_2_3
    · exact s36_2_4
    · exact s36_2_5
    · exact s36_2_6
    · exact s36_2_7
  · fin_cases v
    · exact s36_3_0
    · exact s36_3_1
    · exact s36_3_2
    · exact s36_3_3
    · exact s36_3_4
    · exact s36_3_5
    · exact s36_3_6
    · exact s36_3_7
  · fin_cases v
    · exact s36_4_0
    · exact s36_4_1
    · exact s36_4_2
    · exact s36_4_3
    · exact s36_4_4
    · exact s36_4_5
    · exact s36_4_6
    · exact s36_4_7
  · fin_cases v
    · exact s36_5_0
    · exact s36_5_1
    · exact s36_5_2
    · exact s36_5_3
    · exact s36_5_4
    · exact s36_5_5
    · exact s36_5_6
    · exact s36_5_7
  · exact List.all_eq_true.mp col36_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col36_7 v (List.mem_finRange v)
theorem col37_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 0 v) = true := by decide +kernel
theorem col37_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 1 v) = true := by decide +kernel
theorem s37_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 0 = true := by decide +kernel
theorem s37_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 1 = true := by decide +kernel
theorem s37_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 2 = true := by decide +kernel
theorem s37_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 3 = true := by decide +kernel
theorem k37_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k37_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k37_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s37_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k37_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k37_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k37_2_4_80 k h.1 (by omega)
theorem s37_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 5 = true := by decide +kernel
theorem s37_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 6 = true := by decide +kernel
theorem s37_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 2 7 = true := by decide +kernel
theorem s37_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 0 = true := by decide +kernel
theorem s37_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 1 = true := by decide +kernel
theorem s37_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 2 = true := by decide +kernel
theorem s37_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 3 = true := by decide +kernel
theorem k37_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k37_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k37_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s37_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k37_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k37_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 37) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (37 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k37_3_4_80 k h.1 (by omega)
theorem s37_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 5 = true := by decide +kernel
theorem s37_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 6 = true := by decide +kernel
theorem s37_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 3 7 = true := by decide +kernel
theorem s37_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 0 = true := by decide +kernel
theorem s37_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 1 = true := by decide +kernel
theorem s37_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 2 = true := by decide +kernel
theorem s37_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 3 = true := by decide +kernel
theorem s37_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 4 = true := by decide +kernel
theorem k37_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k37_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k37_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k37_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k37_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k37_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k37_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k37_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k37_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s37_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k37_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k37_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k37_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k37_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k37_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k37_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k37_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k37_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 5).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k37_4_5_40 k h.1 (by omega)
theorem k37_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k37_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k37_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k37_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k37_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k37_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k37_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k37_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k37_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k37_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k37_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s37_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k37_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k37_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k37_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k37_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k37_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k37_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k37_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k37_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k37_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k37_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 4 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k37_4_6_50 k h.1 (by omega)
theorem s37_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 4 7 = true := by decide +kernel
theorem s37_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 0 = true := by decide +kernel
theorem s37_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 1 = true := by decide +kernel
theorem s37_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 2 = true := by decide +kernel
theorem s37_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 3 = true := by decide +kernel
theorem s37_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 4 = true := by decide +kernel
theorem s37_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 5 = true := by decide +kernel
theorem k37_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k37_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k37_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k37_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k37_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k37_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s37_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k37_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k37_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k37_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k37_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k37_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 37) ((InDA2.TCasaD 4 5 6).getD (37 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k37_5_6_50 k h.1 (by omega)
theorem s37_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 5 7 = true := by decide +kernel
theorem col37_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 6 v) = true := by decide +kernel
theorem col37_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 7 v) = true := by decide +kernel
theorem col37 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 37) 37 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col37_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col37_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s37_2_0
    · exact s37_2_1
    · exact s37_2_2
    · exact s37_2_3
    · exact s37_2_4
    · exact s37_2_5
    · exact s37_2_6
    · exact s37_2_7
  · fin_cases v
    · exact s37_3_0
    · exact s37_3_1
    · exact s37_3_2
    · exact s37_3_3
    · exact s37_3_4
    · exact s37_3_5
    · exact s37_3_6
    · exact s37_3_7
  · fin_cases v
    · exact s37_4_0
    · exact s37_4_1
    · exact s37_4_2
    · exact s37_4_3
    · exact s37_4_4
    · exact s37_4_5
    · exact s37_4_6
    · exact s37_4_7
  · fin_cases v
    · exact s37_5_0
    · exact s37_5_1
    · exact s37_5_2
    · exact s37_5_3
    · exact s37_5_4
    · exact s37_5_5
    · exact s37_5_6
    · exact s37_5_7
  · exact List.all_eq_true.mp col37_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col37_7 v (List.mem_finRange v)
theorem col38_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 0 v) = true := by decide +kernel
theorem col38_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 1 v) = true := by decide +kernel
theorem s38_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 0 = true := by decide +kernel
theorem s38_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 1 = true := by decide +kernel
theorem s38_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 2 = true := by decide +kernel
theorem s38_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 3 = true := by decide +kernel
theorem k38_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k38_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k38_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s38_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k38_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k38_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k38_2_4_80 k h.1 (by omega)
theorem s38_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 5 = true := by decide +kernel
theorem s38_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 6 = true := by decide +kernel
theorem s38_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 2 7 = true := by decide +kernel
theorem s38_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 0 = true := by decide +kernel
theorem s38_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 1 = true := by decide +kernel
theorem s38_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 2 = true := by decide +kernel
theorem s38_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 3 = true := by decide +kernel
theorem k38_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k38_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k38_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s38_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k38_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k38_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 38) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (38 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k38_3_4_80 k h.1 (by omega)
theorem s38_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 5 = true := by decide +kernel
theorem s38_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 6 = true := by decide +kernel
theorem s38_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 3 7 = true := by decide +kernel
theorem s38_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 0 = true := by decide +kernel
theorem s38_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 1 = true := by decide +kernel
theorem s38_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 2 = true := by decide +kernel
theorem s38_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 3 = true := by decide +kernel
theorem s38_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 4 = true := by decide +kernel
theorem k38_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k38_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k38_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k38_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k38_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k38_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k38_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k38_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k38_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s38_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k38_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k38_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k38_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k38_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k38_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k38_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k38_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k38_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 5).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k38_4_5_40 k h.1 (by omega)
theorem k38_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k38_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k38_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k38_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k38_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k38_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k38_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k38_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k38_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k38_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k38_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s38_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k38_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k38_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k38_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k38_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k38_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k38_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k38_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k38_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k38_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k38_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 4 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k38_4_6_50 k h.1 (by omega)
theorem s38_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 4 7 = true := by decide +kernel
theorem s38_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 0 = true := by decide +kernel
theorem s38_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 1 = true := by decide +kernel
theorem s38_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 2 = true := by decide +kernel
theorem s38_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 3 = true := by decide +kernel
theorem s38_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 4 = true := by decide +kernel
theorem s38_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 5 = true := by decide +kernel
theorem k38_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k38_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k38_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k38_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k38_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k38_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s38_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k38_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k38_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k38_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k38_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k38_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 38) ((InDA2.TCasaD 4 5 6).getD (38 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k38_5_6_50 k h.1 (by omega)
theorem s38_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 5 7 = true := by decide +kernel
theorem col38_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 6 v) = true := by decide +kernel
theorem col38_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 7 v) = true := by decide +kernel
theorem col38 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 38) 38 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col38_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col38_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s38_2_0
    · exact s38_2_1
    · exact s38_2_2
    · exact s38_2_3
    · exact s38_2_4
    · exact s38_2_5
    · exact s38_2_6
    · exact s38_2_7
  · fin_cases v
    · exact s38_3_0
    · exact s38_3_1
    · exact s38_3_2
    · exact s38_3_3
    · exact s38_3_4
    · exact s38_3_5
    · exact s38_3_6
    · exact s38_3_7
  · fin_cases v
    · exact s38_4_0
    · exact s38_4_1
    · exact s38_4_2
    · exact s38_4_3
    · exact s38_4_4
    · exact s38_4_5
    · exact s38_4_6
    · exact s38_4_7
  · fin_cases v
    · exact s38_5_0
    · exact s38_5_1
    · exact s38_5_2
    · exact s38_5_3
    · exact s38_5_4
    · exact s38_5_5
    · exact s38_5_6
    · exact s38_5_7
  · exact List.all_eq_true.mp col38_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col38_7 v (List.mem_finRange v)
theorem col39_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 0 v) = true := by decide +kernel
theorem col39_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 1 v) = true := by decide +kernel
theorem s39_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 0 = true := by decide +kernel
theorem s39_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 1 = true := by decide +kernel
theorem s39_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 2 = true := by decide +kernel
theorem s39_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 3 = true := by decide +kernel
theorem k39_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k39_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k39_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s39_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k39_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k39_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k39_2_4_80 k h.1 (by omega)
theorem s39_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 5 = true := by decide +kernel
theorem s39_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 6 = true := by decide +kernel
theorem s39_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 2 7 = true := by decide +kernel
theorem s39_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 0 = true := by decide +kernel
theorem s39_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 1 = true := by decide +kernel
theorem s39_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 2 = true := by decide +kernel
theorem s39_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 3 = true := by decide +kernel
theorem k39_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k39_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k39_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s39_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k39_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k39_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 39) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (39 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k39_3_4_80 k h.1 (by omega)
theorem s39_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 5 = true := by decide +kernel
theorem s39_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 6 = true := by decide +kernel
theorem s39_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 3 7 = true := by decide +kernel
theorem s39_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 0 = true := by decide +kernel
theorem s39_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 1 = true := by decide +kernel
theorem s39_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 2 = true := by decide +kernel
theorem s39_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 3 = true := by decide +kernel
theorem s39_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 4 = true := by decide +kernel
theorem k39_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k39_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k39_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k39_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k39_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k39_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k39_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k39_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k39_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s39_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k39_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k39_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k39_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k39_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k39_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k39_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k39_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k39_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 5).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k39_4_5_40 k h.1 (by omega)
theorem k39_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k39_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k39_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k39_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k39_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k39_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k39_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k39_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k39_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k39_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k39_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s39_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k39_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k39_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k39_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k39_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k39_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k39_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k39_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k39_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k39_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k39_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 4 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k39_4_6_50 k h.1 (by omega)
theorem s39_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 4 7 = true := by decide +kernel
theorem s39_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 0 = true := by decide +kernel
theorem s39_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 1 = true := by decide +kernel
theorem s39_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 2 = true := by decide +kernel
theorem s39_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 3 = true := by decide +kernel
theorem s39_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 4 = true := by decide +kernel
theorem s39_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 5 = true := by decide +kernel
theorem k39_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k39_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k39_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k39_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k39_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k39_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s39_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k39_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k39_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k39_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k39_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k39_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 39) ((InDA2.TCasaD 4 5 6).getD (39 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k39_5_6_50 k h.1 (by omega)
theorem s39_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 5 7 = true := by decide +kernel
theorem col39_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 6 v) = true := by decide +kernel
theorem col39_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 7 v) = true := by decide +kernel
theorem col39 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 39) 39 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col39_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col39_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s39_2_0
    · exact s39_2_1
    · exact s39_2_2
    · exact s39_2_3
    · exact s39_2_4
    · exact s39_2_5
    · exact s39_2_6
    · exact s39_2_7
  · fin_cases v
    · exact s39_3_0
    · exact s39_3_1
    · exact s39_3_2
    · exact s39_3_3
    · exact s39_3_4
    · exact s39_3_5
    · exact s39_3_6
    · exact s39_3_7
  · fin_cases v
    · exact s39_4_0
    · exact s39_4_1
    · exact s39_4_2
    · exact s39_4_3
    · exact s39_4_4
    · exact s39_4_5
    · exact s39_4_6
    · exact s39_4_7
  · fin_cases v
    · exact s39_5_0
    · exact s39_5_1
    · exact s39_5_2
    · exact s39_5_3
    · exact s39_5_4
    · exact s39_5_5
    · exact s39_5_6
    · exact s39_5_7
  · exact List.all_eq_true.mp col39_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col39_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
