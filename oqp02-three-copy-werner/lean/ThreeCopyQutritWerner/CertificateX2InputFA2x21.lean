module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [105, 110). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col105_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 0 v) = true := by decide +kernel
theorem col105_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 1 v) = true := by decide +kernel
theorem s105_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 0 = true := by decide +kernel
theorem s105_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 1 = true := by decide +kernel
theorem s105_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 2 = true := by decide +kernel
theorem s105_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 3 = true := by decide +kernel
theorem k105_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k105_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k105_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s105_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k105_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k105_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k105_2_4_80 k h.1 (by omega)
theorem s105_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 5 = true := by decide +kernel
theorem s105_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 6 = true := by decide +kernel
theorem s105_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 2 7 = true := by decide +kernel
theorem s105_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 0 = true := by decide +kernel
theorem s105_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 1 = true := by decide +kernel
theorem s105_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 2 = true := by decide +kernel
theorem s105_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 3 = true := by decide +kernel
theorem k105_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k105_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k105_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s105_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k105_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k105_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 105) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (105 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k105_3_4_80 k h.1 (by omega)
theorem s105_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 5 = true := by decide +kernel
theorem s105_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 6 = true := by decide +kernel
theorem s105_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 3 7 = true := by decide +kernel
theorem s105_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 0 = true := by decide +kernel
theorem s105_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 1 = true := by decide +kernel
theorem s105_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 2 = true := by decide +kernel
theorem s105_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 3 = true := by decide +kernel
theorem s105_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 4 = true := by decide +kernel
theorem k105_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k105_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k105_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k105_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k105_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k105_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k105_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k105_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k105_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s105_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k105_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k105_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k105_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k105_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k105_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k105_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k105_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k105_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 5).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k105_4_5_40 k h.1 (by omega)
theorem k105_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k105_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k105_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k105_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k105_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k105_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k105_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k105_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k105_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k105_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k105_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s105_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k105_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k105_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k105_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k105_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k105_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k105_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k105_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k105_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k105_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k105_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 4 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k105_4_6_50 k h.1 (by omega)
theorem s105_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 4 7 = true := by decide +kernel
theorem s105_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 0 = true := by decide +kernel
theorem s105_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 1 = true := by decide +kernel
theorem s105_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 2 = true := by decide +kernel
theorem s105_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 3 = true := by decide +kernel
theorem s105_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 4 = true := by decide +kernel
theorem s105_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 5 = true := by decide +kernel
theorem k105_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k105_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k105_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k105_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k105_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k105_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s105_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k105_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k105_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k105_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k105_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k105_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 105) ((InDA2.TCasaD 4 5 6).getD (105 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k105_5_6_50 k h.1 (by omega)
theorem s105_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 5 7 = true := by decide +kernel
theorem col105_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 6 v) = true := by decide +kernel
theorem col105_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 7 v) = true := by decide +kernel
theorem col105 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 105) 105 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col105_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col105_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s105_2_0
    · exact s105_2_1
    · exact s105_2_2
    · exact s105_2_3
    · exact s105_2_4
    · exact s105_2_5
    · exact s105_2_6
    · exact s105_2_7
  · fin_cases v
    · exact s105_3_0
    · exact s105_3_1
    · exact s105_3_2
    · exact s105_3_3
    · exact s105_3_4
    · exact s105_3_5
    · exact s105_3_6
    · exact s105_3_7
  · fin_cases v
    · exact s105_4_0
    · exact s105_4_1
    · exact s105_4_2
    · exact s105_4_3
    · exact s105_4_4
    · exact s105_4_5
    · exact s105_4_6
    · exact s105_4_7
  · fin_cases v
    · exact s105_5_0
    · exact s105_5_1
    · exact s105_5_2
    · exact s105_5_3
    · exact s105_5_4
    · exact s105_5_5
    · exact s105_5_6
    · exact s105_5_7
  · exact List.all_eq_true.mp col105_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col105_7 v (List.mem_finRange v)
theorem col106_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 0 v) = true := by decide +kernel
theorem col106_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 1 v) = true := by decide +kernel
theorem s106_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 0 = true := by decide +kernel
theorem s106_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 1 = true := by decide +kernel
theorem s106_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 2 = true := by decide +kernel
theorem s106_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 3 = true := by decide +kernel
theorem k106_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k106_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k106_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s106_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k106_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k106_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k106_2_4_80 k h.1 (by omega)
theorem s106_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 5 = true := by decide +kernel
theorem s106_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 6 = true := by decide +kernel
theorem s106_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 2 7 = true := by decide +kernel
theorem s106_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 0 = true := by decide +kernel
theorem s106_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 1 = true := by decide +kernel
theorem s106_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 2 = true := by decide +kernel
theorem s106_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 3 = true := by decide +kernel
theorem k106_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k106_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k106_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s106_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k106_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k106_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 106) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (106 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k106_3_4_80 k h.1 (by omega)
theorem s106_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 5 = true := by decide +kernel
theorem s106_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 6 = true := by decide +kernel
theorem s106_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 3 7 = true := by decide +kernel
theorem s106_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 0 = true := by decide +kernel
theorem s106_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 1 = true := by decide +kernel
theorem s106_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 2 = true := by decide +kernel
theorem s106_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 3 = true := by decide +kernel
theorem s106_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 4 = true := by decide +kernel
theorem k106_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k106_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k106_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k106_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k106_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k106_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k106_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k106_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k106_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s106_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k106_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k106_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k106_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k106_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k106_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k106_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k106_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k106_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 5).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k106_4_5_40 k h.1 (by omega)
theorem k106_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k106_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k106_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k106_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k106_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k106_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k106_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k106_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k106_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k106_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k106_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s106_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k106_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k106_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k106_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k106_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k106_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k106_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k106_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k106_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k106_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k106_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 4 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k106_4_6_50 k h.1 (by omega)
theorem s106_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 4 7 = true := by decide +kernel
theorem s106_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 0 = true := by decide +kernel
theorem s106_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 1 = true := by decide +kernel
theorem s106_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 2 = true := by decide +kernel
theorem s106_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 3 = true := by decide +kernel
theorem s106_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 4 = true := by decide +kernel
theorem s106_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 5 = true := by decide +kernel
theorem k106_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k106_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k106_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k106_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k106_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k106_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s106_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k106_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k106_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k106_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k106_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k106_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 106) ((InDA2.TCasaD 4 5 6).getD (106 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k106_5_6_50 k h.1 (by omega)
theorem s106_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 5 7 = true := by decide +kernel
theorem col106_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 6 v) = true := by decide +kernel
theorem col106_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 7 v) = true := by decide +kernel
theorem col106 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 106) 106 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col106_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col106_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s106_2_0
    · exact s106_2_1
    · exact s106_2_2
    · exact s106_2_3
    · exact s106_2_4
    · exact s106_2_5
    · exact s106_2_6
    · exact s106_2_7
  · fin_cases v
    · exact s106_3_0
    · exact s106_3_1
    · exact s106_3_2
    · exact s106_3_3
    · exact s106_3_4
    · exact s106_3_5
    · exact s106_3_6
    · exact s106_3_7
  · fin_cases v
    · exact s106_4_0
    · exact s106_4_1
    · exact s106_4_2
    · exact s106_4_3
    · exact s106_4_4
    · exact s106_4_5
    · exact s106_4_6
    · exact s106_4_7
  · fin_cases v
    · exact s106_5_0
    · exact s106_5_1
    · exact s106_5_2
    · exact s106_5_3
    · exact s106_5_4
    · exact s106_5_5
    · exact s106_5_6
    · exact s106_5_7
  · exact List.all_eq_true.mp col106_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col106_7 v (List.mem_finRange v)
theorem col107_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 0 v) = true := by decide +kernel
theorem col107_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 1 v) = true := by decide +kernel
theorem s107_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 0 = true := by decide +kernel
theorem s107_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 1 = true := by decide +kernel
theorem s107_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 2 = true := by decide +kernel
theorem s107_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 3 = true := by decide +kernel
theorem k107_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k107_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k107_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s107_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k107_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k107_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k107_2_4_80 k h.1 (by omega)
theorem s107_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 5 = true := by decide +kernel
theorem s107_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 6 = true := by decide +kernel
theorem s107_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 2 7 = true := by decide +kernel
theorem s107_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 0 = true := by decide +kernel
theorem s107_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 1 = true := by decide +kernel
theorem s107_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 2 = true := by decide +kernel
theorem s107_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 3 = true := by decide +kernel
theorem k107_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k107_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k107_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s107_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k107_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k107_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 107) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (107 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k107_3_4_80 k h.1 (by omega)
theorem s107_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 5 = true := by decide +kernel
theorem s107_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 6 = true := by decide +kernel
theorem s107_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 3 7 = true := by decide +kernel
theorem s107_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 0 = true := by decide +kernel
theorem s107_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 1 = true := by decide +kernel
theorem s107_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 2 = true := by decide +kernel
theorem s107_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 3 = true := by decide +kernel
theorem s107_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 4 = true := by decide +kernel
theorem k107_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k107_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k107_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k107_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k107_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k107_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k107_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k107_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k107_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s107_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k107_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k107_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k107_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k107_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k107_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k107_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k107_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k107_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 5).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k107_4_5_40 k h.1 (by omega)
theorem k107_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k107_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k107_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k107_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k107_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k107_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k107_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k107_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k107_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k107_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k107_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s107_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k107_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k107_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k107_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k107_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k107_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k107_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k107_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k107_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k107_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k107_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 4 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k107_4_6_50 k h.1 (by omega)
theorem s107_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 4 7 = true := by decide +kernel
theorem s107_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 0 = true := by decide +kernel
theorem s107_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 1 = true := by decide +kernel
theorem s107_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 2 = true := by decide +kernel
theorem s107_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 3 = true := by decide +kernel
theorem s107_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 4 = true := by decide +kernel
theorem s107_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 5 = true := by decide +kernel
theorem k107_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k107_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k107_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k107_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k107_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k107_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s107_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k107_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k107_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k107_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k107_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k107_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 107) ((InDA2.TCasaD 4 5 6).getD (107 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k107_5_6_50 k h.1 (by omega)
theorem s107_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 5 7 = true := by decide +kernel
theorem col107_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 6 v) = true := by decide +kernel
theorem col107_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 7 v) = true := by decide +kernel
theorem col107 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 107) 107 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col107_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col107_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s107_2_0
    · exact s107_2_1
    · exact s107_2_2
    · exact s107_2_3
    · exact s107_2_4
    · exact s107_2_5
    · exact s107_2_6
    · exact s107_2_7
  · fin_cases v
    · exact s107_3_0
    · exact s107_3_1
    · exact s107_3_2
    · exact s107_3_3
    · exact s107_3_4
    · exact s107_3_5
    · exact s107_3_6
    · exact s107_3_7
  · fin_cases v
    · exact s107_4_0
    · exact s107_4_1
    · exact s107_4_2
    · exact s107_4_3
    · exact s107_4_4
    · exact s107_4_5
    · exact s107_4_6
    · exact s107_4_7
  · fin_cases v
    · exact s107_5_0
    · exact s107_5_1
    · exact s107_5_2
    · exact s107_5_3
    · exact s107_5_4
    · exact s107_5_5
    · exact s107_5_6
    · exact s107_5_7
  · exact List.all_eq_true.mp col107_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col107_7 v (List.mem_finRange v)
theorem col108_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 0 v) = true := by decide +kernel
theorem col108_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 1 v) = true := by decide +kernel
theorem s108_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 0 = true := by decide +kernel
theorem s108_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 1 = true := by decide +kernel
theorem s108_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 2 = true := by decide +kernel
theorem s108_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 3 = true := by decide +kernel
theorem k108_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k108_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k108_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s108_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k108_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k108_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k108_2_4_80 k h.1 (by omega)
theorem s108_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 5 = true := by decide +kernel
theorem s108_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 6 = true := by decide +kernel
theorem s108_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 2 7 = true := by decide +kernel
theorem s108_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 0 = true := by decide +kernel
theorem s108_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 1 = true := by decide +kernel
theorem s108_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 2 = true := by decide +kernel
theorem s108_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 3 = true := by decide +kernel
theorem k108_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k108_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k108_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s108_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k108_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k108_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 108) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (108 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k108_3_4_80 k h.1 (by omega)
theorem s108_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 5 = true := by decide +kernel
theorem s108_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 6 = true := by decide +kernel
theorem s108_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 3 7 = true := by decide +kernel
theorem s108_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 0 = true := by decide +kernel
theorem s108_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 1 = true := by decide +kernel
theorem s108_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 2 = true := by decide +kernel
theorem s108_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 3 = true := by decide +kernel
theorem s108_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 4 = true := by decide +kernel
theorem k108_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k108_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k108_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k108_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k108_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k108_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k108_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k108_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k108_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s108_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k108_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k108_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k108_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k108_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k108_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k108_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k108_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k108_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 5).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k108_4_5_40 k h.1 (by omega)
theorem k108_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k108_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k108_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k108_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k108_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k108_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k108_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k108_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k108_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k108_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k108_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s108_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k108_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k108_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k108_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k108_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k108_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k108_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k108_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k108_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k108_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k108_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 4 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k108_4_6_50 k h.1 (by omega)
theorem s108_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 4 7 = true := by decide +kernel
theorem s108_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 0 = true := by decide +kernel
theorem s108_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 1 = true := by decide +kernel
theorem s108_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 2 = true := by decide +kernel
theorem s108_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 3 = true := by decide +kernel
theorem s108_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 4 = true := by decide +kernel
theorem s108_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 5 = true := by decide +kernel
theorem k108_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k108_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k108_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k108_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k108_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k108_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s108_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k108_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k108_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k108_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k108_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k108_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 108) ((InDA2.TCasaD 4 5 6).getD (108 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k108_5_6_50 k h.1 (by omega)
theorem s108_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 5 7 = true := by decide +kernel
theorem col108_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 6 v) = true := by decide +kernel
theorem col108_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 7 v) = true := by decide +kernel
theorem col108 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 108) 108 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col108_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col108_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s108_2_0
    · exact s108_2_1
    · exact s108_2_2
    · exact s108_2_3
    · exact s108_2_4
    · exact s108_2_5
    · exact s108_2_6
    · exact s108_2_7
  · fin_cases v
    · exact s108_3_0
    · exact s108_3_1
    · exact s108_3_2
    · exact s108_3_3
    · exact s108_3_4
    · exact s108_3_5
    · exact s108_3_6
    · exact s108_3_7
  · fin_cases v
    · exact s108_4_0
    · exact s108_4_1
    · exact s108_4_2
    · exact s108_4_3
    · exact s108_4_4
    · exact s108_4_5
    · exact s108_4_6
    · exact s108_4_7
  · fin_cases v
    · exact s108_5_0
    · exact s108_5_1
    · exact s108_5_2
    · exact s108_5_3
    · exact s108_5_4
    · exact s108_5_5
    · exact s108_5_6
    · exact s108_5_7
  · exact List.all_eq_true.mp col108_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col108_7 v (List.mem_finRange v)
theorem col109_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 0 v) = true := by decide +kernel
theorem col109_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 1 v) = true := by decide +kernel
theorem s109_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 0 = true := by decide +kernel
theorem s109_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 1 = true := by decide +kernel
theorem s109_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 2 = true := by decide +kernel
theorem s109_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 3 = true := by decide +kernel
theorem k109_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k109_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k109_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s109_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k109_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k109_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k109_2_4_80 k h.1 (by omega)
theorem s109_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 5 = true := by decide +kernel
theorem s109_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 6 = true := by decide +kernel
theorem s109_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 2 7 = true := by decide +kernel
theorem s109_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 0 = true := by decide +kernel
theorem s109_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 1 = true := by decide +kernel
theorem s109_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 2 = true := by decide +kernel
theorem s109_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 3 = true := by decide +kernel
theorem k109_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k109_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k109_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s109_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k109_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k109_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 109) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (109 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k109_3_4_80 k h.1 (by omega)
theorem s109_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 5 = true := by decide +kernel
theorem s109_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 6 = true := by decide +kernel
theorem s109_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 3 7 = true := by decide +kernel
theorem s109_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 0 = true := by decide +kernel
theorem s109_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 1 = true := by decide +kernel
theorem s109_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 2 = true := by decide +kernel
theorem s109_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 3 = true := by decide +kernel
theorem s109_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 4 = true := by decide +kernel
theorem k109_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k109_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k109_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k109_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k109_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k109_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k109_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k109_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k109_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s109_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k109_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k109_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k109_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k109_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k109_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k109_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k109_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k109_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 5).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k109_4_5_40 k h.1 (by omega)
theorem k109_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k109_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k109_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k109_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k109_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k109_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k109_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k109_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k109_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k109_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k109_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s109_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k109_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k109_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k109_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k109_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k109_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k109_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k109_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k109_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k109_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k109_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 4 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k109_4_6_50 k h.1 (by omega)
theorem s109_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 4 7 = true := by decide +kernel
theorem s109_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 0 = true := by decide +kernel
theorem s109_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 1 = true := by decide +kernel
theorem s109_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 2 = true := by decide +kernel
theorem s109_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 3 = true := by decide +kernel
theorem s109_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 4 = true := by decide +kernel
theorem s109_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 5 = true := by decide +kernel
theorem k109_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k109_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k109_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k109_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k109_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k109_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s109_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k109_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k109_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k109_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k109_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k109_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 109) ((InDA2.TCasaD 4 5 6).getD (109 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k109_5_6_50 k h.1 (by omega)
theorem s109_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 5 7 = true := by decide +kernel
theorem col109_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 6 v) = true := by decide +kernel
theorem col109_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 7 v) = true := by decide +kernel
theorem col109 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 109) 109 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col109_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col109_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s109_2_0
    · exact s109_2_1
    · exact s109_2_2
    · exact s109_2_3
    · exact s109_2_4
    · exact s109_2_5
    · exact s109_2_6
    · exact s109_2_7
  · fin_cases v
    · exact s109_3_0
    · exact s109_3_1
    · exact s109_3_2
    · exact s109_3_3
    · exact s109_3_4
    · exact s109_3_5
    · exact s109_3_6
    · exact s109_3_7
  · fin_cases v
    · exact s109_4_0
    · exact s109_4_1
    · exact s109_4_2
    · exact s109_4_3
    · exact s109_4_4
    · exact s109_4_5
    · exact s109_4_6
    · exact s109_4_7
  · fin_cases v
    · exact s109_5_0
    · exact s109_5_1
    · exact s109_5_2
    · exact s109_5_3
    · exact s109_5_4
    · exact s109_5_5
    · exact s109_5_6
    · exact s109_5_7
  · exact List.all_eq_true.mp col109_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col109_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
