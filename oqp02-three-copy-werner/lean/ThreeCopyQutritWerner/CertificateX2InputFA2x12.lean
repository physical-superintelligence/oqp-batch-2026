module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [60, 65). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col60_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 0 v) = true := by decide +kernel
theorem col60_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 1 v) = true := by decide +kernel
theorem s60_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 0 = true := by decide +kernel
theorem s60_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 1 = true := by decide +kernel
theorem s60_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 2 = true := by decide +kernel
theorem s60_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 3 = true := by decide +kernel
theorem k60_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k60_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k60_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s60_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k60_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k60_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k60_2_4_80 k h.1 (by omega)
theorem s60_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 5 = true := by decide +kernel
theorem s60_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 6 = true := by decide +kernel
theorem s60_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 2 7 = true := by decide +kernel
theorem s60_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 0 = true := by decide +kernel
theorem s60_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 1 = true := by decide +kernel
theorem s60_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 2 = true := by decide +kernel
theorem s60_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 3 = true := by decide +kernel
theorem k60_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k60_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k60_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s60_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k60_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k60_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 60) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (60 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k60_3_4_80 k h.1 (by omega)
theorem s60_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 5 = true := by decide +kernel
theorem s60_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 6 = true := by decide +kernel
theorem s60_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 3 7 = true := by decide +kernel
theorem s60_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 0 = true := by decide +kernel
theorem s60_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 1 = true := by decide +kernel
theorem s60_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 2 = true := by decide +kernel
theorem s60_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 3 = true := by decide +kernel
theorem s60_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 4 = true := by decide +kernel
theorem k60_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k60_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k60_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k60_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k60_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k60_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k60_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k60_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k60_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s60_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k60_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k60_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k60_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k60_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k60_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k60_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k60_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k60_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 5).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k60_4_5_40 k h.1 (by omega)
theorem k60_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k60_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k60_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k60_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k60_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k60_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k60_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k60_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k60_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k60_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k60_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s60_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k60_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k60_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k60_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k60_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k60_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k60_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k60_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k60_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k60_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k60_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 4 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k60_4_6_50 k h.1 (by omega)
theorem s60_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 4 7 = true := by decide +kernel
theorem s60_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 0 = true := by decide +kernel
theorem s60_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 1 = true := by decide +kernel
theorem s60_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 2 = true := by decide +kernel
theorem s60_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 3 = true := by decide +kernel
theorem s60_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 4 = true := by decide +kernel
theorem s60_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 5 = true := by decide +kernel
theorem k60_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k60_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k60_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k60_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k60_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k60_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s60_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k60_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k60_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k60_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k60_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k60_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 60) ((InDA2.TCasaD 4 5 6).getD (60 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k60_5_6_50 k h.1 (by omega)
theorem s60_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 5 7 = true := by decide +kernel
theorem col60_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 6 v) = true := by decide +kernel
theorem col60_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 7 v) = true := by decide +kernel
theorem col60 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 60) 60 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col60_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col60_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s60_2_0
    · exact s60_2_1
    · exact s60_2_2
    · exact s60_2_3
    · exact s60_2_4
    · exact s60_2_5
    · exact s60_2_6
    · exact s60_2_7
  · fin_cases v
    · exact s60_3_0
    · exact s60_3_1
    · exact s60_3_2
    · exact s60_3_3
    · exact s60_3_4
    · exact s60_3_5
    · exact s60_3_6
    · exact s60_3_7
  · fin_cases v
    · exact s60_4_0
    · exact s60_4_1
    · exact s60_4_2
    · exact s60_4_3
    · exact s60_4_4
    · exact s60_4_5
    · exact s60_4_6
    · exact s60_4_7
  · fin_cases v
    · exact s60_5_0
    · exact s60_5_1
    · exact s60_5_2
    · exact s60_5_3
    · exact s60_5_4
    · exact s60_5_5
    · exact s60_5_6
    · exact s60_5_7
  · exact List.all_eq_true.mp col60_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col60_7 v (List.mem_finRange v)
theorem col61_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 0 v) = true := by decide +kernel
theorem col61_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 1 v) = true := by decide +kernel
theorem s61_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 0 = true := by decide +kernel
theorem s61_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 1 = true := by decide +kernel
theorem s61_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 2 = true := by decide +kernel
theorem s61_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 3 = true := by decide +kernel
theorem k61_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k61_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k61_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s61_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k61_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k61_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k61_2_4_80 k h.1 (by omega)
theorem s61_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 5 = true := by decide +kernel
theorem s61_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 6 = true := by decide +kernel
theorem s61_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 2 7 = true := by decide +kernel
theorem s61_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 0 = true := by decide +kernel
theorem s61_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 1 = true := by decide +kernel
theorem s61_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 2 = true := by decide +kernel
theorem s61_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 3 = true := by decide +kernel
theorem k61_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k61_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k61_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s61_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k61_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k61_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 61) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (61 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k61_3_4_80 k h.1 (by omega)
theorem s61_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 5 = true := by decide +kernel
theorem s61_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 6 = true := by decide +kernel
theorem s61_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 3 7 = true := by decide +kernel
theorem s61_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 0 = true := by decide +kernel
theorem s61_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 1 = true := by decide +kernel
theorem s61_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 2 = true := by decide +kernel
theorem s61_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 3 = true := by decide +kernel
theorem s61_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 4 = true := by decide +kernel
theorem k61_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k61_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k61_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k61_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k61_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k61_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k61_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k61_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k61_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s61_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k61_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k61_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k61_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k61_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k61_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k61_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k61_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k61_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 5).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k61_4_5_40 k h.1 (by omega)
theorem k61_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k61_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k61_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k61_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k61_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k61_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k61_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k61_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k61_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k61_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k61_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s61_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k61_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k61_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k61_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k61_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k61_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k61_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k61_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k61_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k61_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k61_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 4 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k61_4_6_50 k h.1 (by omega)
theorem s61_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 4 7 = true := by decide +kernel
theorem s61_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 0 = true := by decide +kernel
theorem s61_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 1 = true := by decide +kernel
theorem s61_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 2 = true := by decide +kernel
theorem s61_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 3 = true := by decide +kernel
theorem s61_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 4 = true := by decide +kernel
theorem s61_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 5 = true := by decide +kernel
theorem k61_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k61_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k61_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k61_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k61_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k61_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s61_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k61_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k61_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k61_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k61_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k61_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 61) ((InDA2.TCasaD 4 5 6).getD (61 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k61_5_6_50 k h.1 (by omega)
theorem s61_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 5 7 = true := by decide +kernel
theorem col61_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 6 v) = true := by decide +kernel
theorem col61_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 7 v) = true := by decide +kernel
theorem col61 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 61) 61 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col61_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col61_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s61_2_0
    · exact s61_2_1
    · exact s61_2_2
    · exact s61_2_3
    · exact s61_2_4
    · exact s61_2_5
    · exact s61_2_6
    · exact s61_2_7
  · fin_cases v
    · exact s61_3_0
    · exact s61_3_1
    · exact s61_3_2
    · exact s61_3_3
    · exact s61_3_4
    · exact s61_3_5
    · exact s61_3_6
    · exact s61_3_7
  · fin_cases v
    · exact s61_4_0
    · exact s61_4_1
    · exact s61_4_2
    · exact s61_4_3
    · exact s61_4_4
    · exact s61_4_5
    · exact s61_4_6
    · exact s61_4_7
  · fin_cases v
    · exact s61_5_0
    · exact s61_5_1
    · exact s61_5_2
    · exact s61_5_3
    · exact s61_5_4
    · exact s61_5_5
    · exact s61_5_6
    · exact s61_5_7
  · exact List.all_eq_true.mp col61_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col61_7 v (List.mem_finRange v)
theorem col62_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 0 v) = true := by decide +kernel
theorem col62_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 1 v) = true := by decide +kernel
theorem s62_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 0 = true := by decide +kernel
theorem s62_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 1 = true := by decide +kernel
theorem s62_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 2 = true := by decide +kernel
theorem s62_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 3 = true := by decide +kernel
theorem k62_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k62_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k62_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s62_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k62_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k62_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k62_2_4_80 k h.1 (by omega)
theorem s62_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 5 = true := by decide +kernel
theorem s62_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 6 = true := by decide +kernel
theorem s62_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 2 7 = true := by decide +kernel
theorem s62_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 0 = true := by decide +kernel
theorem s62_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 1 = true := by decide +kernel
theorem s62_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 2 = true := by decide +kernel
theorem s62_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 3 = true := by decide +kernel
theorem k62_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k62_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k62_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s62_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k62_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k62_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 62) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (62 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k62_3_4_80 k h.1 (by omega)
theorem s62_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 5 = true := by decide +kernel
theorem s62_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 6 = true := by decide +kernel
theorem s62_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 3 7 = true := by decide +kernel
theorem s62_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 0 = true := by decide +kernel
theorem s62_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 1 = true := by decide +kernel
theorem s62_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 2 = true := by decide +kernel
theorem s62_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 3 = true := by decide +kernel
theorem s62_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 4 = true := by decide +kernel
theorem k62_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k62_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k62_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k62_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k62_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k62_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k62_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k62_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k62_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s62_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k62_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k62_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k62_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k62_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k62_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k62_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k62_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k62_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 5).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k62_4_5_40 k h.1 (by omega)
theorem k62_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k62_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k62_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k62_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k62_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k62_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k62_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k62_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k62_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k62_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k62_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s62_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k62_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k62_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k62_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k62_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k62_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k62_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k62_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k62_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k62_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k62_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 4 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k62_4_6_50 k h.1 (by omega)
theorem s62_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 4 7 = true := by decide +kernel
theorem s62_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 0 = true := by decide +kernel
theorem s62_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 1 = true := by decide +kernel
theorem s62_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 2 = true := by decide +kernel
theorem s62_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 3 = true := by decide +kernel
theorem s62_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 4 = true := by decide +kernel
theorem s62_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 5 = true := by decide +kernel
theorem k62_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k62_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k62_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k62_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k62_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k62_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s62_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k62_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k62_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k62_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k62_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k62_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 62) ((InDA2.TCasaD 4 5 6).getD (62 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k62_5_6_50 k h.1 (by omega)
theorem s62_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 5 7 = true := by decide +kernel
theorem col62_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 6 v) = true := by decide +kernel
theorem col62_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 7 v) = true := by decide +kernel
theorem col62 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 62) 62 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col62_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col62_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s62_2_0
    · exact s62_2_1
    · exact s62_2_2
    · exact s62_2_3
    · exact s62_2_4
    · exact s62_2_5
    · exact s62_2_6
    · exact s62_2_7
  · fin_cases v
    · exact s62_3_0
    · exact s62_3_1
    · exact s62_3_2
    · exact s62_3_3
    · exact s62_3_4
    · exact s62_3_5
    · exact s62_3_6
    · exact s62_3_7
  · fin_cases v
    · exact s62_4_0
    · exact s62_4_1
    · exact s62_4_2
    · exact s62_4_3
    · exact s62_4_4
    · exact s62_4_5
    · exact s62_4_6
    · exact s62_4_7
  · fin_cases v
    · exact s62_5_0
    · exact s62_5_1
    · exact s62_5_2
    · exact s62_5_3
    · exact s62_5_4
    · exact s62_5_5
    · exact s62_5_6
    · exact s62_5_7
  · exact List.all_eq_true.mp col62_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col62_7 v (List.mem_finRange v)
theorem col63_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 0 v) = true := by decide +kernel
theorem col63_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 1 v) = true := by decide +kernel
theorem s63_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 0 = true := by decide +kernel
theorem s63_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 1 = true := by decide +kernel
theorem s63_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 2 = true := by decide +kernel
theorem s63_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 3 = true := by decide +kernel
theorem k63_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k63_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k63_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s63_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k63_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k63_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k63_2_4_80 k h.1 (by omega)
theorem s63_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 5 = true := by decide +kernel
theorem s63_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 6 = true := by decide +kernel
theorem s63_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 2 7 = true := by decide +kernel
theorem s63_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 0 = true := by decide +kernel
theorem s63_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 1 = true := by decide +kernel
theorem s63_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 2 = true := by decide +kernel
theorem s63_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 3 = true := by decide +kernel
theorem k63_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k63_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k63_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s63_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k63_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k63_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 63) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (63 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k63_3_4_80 k h.1 (by omega)
theorem s63_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 5 = true := by decide +kernel
theorem s63_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 6 = true := by decide +kernel
theorem s63_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 3 7 = true := by decide +kernel
theorem s63_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 0 = true := by decide +kernel
theorem s63_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 1 = true := by decide +kernel
theorem s63_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 2 = true := by decide +kernel
theorem s63_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 3 = true := by decide +kernel
theorem s63_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 4 = true := by decide +kernel
theorem k63_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k63_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k63_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k63_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k63_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k63_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k63_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k63_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k63_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s63_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k63_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k63_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k63_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k63_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k63_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k63_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k63_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k63_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 5).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k63_4_5_40 k h.1 (by omega)
theorem k63_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k63_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k63_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k63_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k63_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k63_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k63_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k63_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k63_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k63_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k63_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s63_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k63_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k63_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k63_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k63_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k63_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k63_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k63_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k63_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k63_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k63_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 4 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k63_4_6_50 k h.1 (by omega)
theorem s63_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 4 7 = true := by decide +kernel
theorem s63_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 0 = true := by decide +kernel
theorem s63_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 1 = true := by decide +kernel
theorem s63_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 2 = true := by decide +kernel
theorem s63_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 3 = true := by decide +kernel
theorem s63_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 4 = true := by decide +kernel
theorem s63_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 5 = true := by decide +kernel
theorem k63_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k63_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k63_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k63_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k63_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k63_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s63_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k63_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k63_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k63_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k63_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k63_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 63) ((InDA2.TCasaD 4 5 6).getD (63 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k63_5_6_50 k h.1 (by omega)
theorem s63_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 5 7 = true := by decide +kernel
theorem col63_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 6 v) = true := by decide +kernel
theorem col63_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 7 v) = true := by decide +kernel
theorem col63 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 63) 63 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col63_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col63_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s63_2_0
    · exact s63_2_1
    · exact s63_2_2
    · exact s63_2_3
    · exact s63_2_4
    · exact s63_2_5
    · exact s63_2_6
    · exact s63_2_7
  · fin_cases v
    · exact s63_3_0
    · exact s63_3_1
    · exact s63_3_2
    · exact s63_3_3
    · exact s63_3_4
    · exact s63_3_5
    · exact s63_3_6
    · exact s63_3_7
  · fin_cases v
    · exact s63_4_0
    · exact s63_4_1
    · exact s63_4_2
    · exact s63_4_3
    · exact s63_4_4
    · exact s63_4_5
    · exact s63_4_6
    · exact s63_4_7
  · fin_cases v
    · exact s63_5_0
    · exact s63_5_1
    · exact s63_5_2
    · exact s63_5_3
    · exact s63_5_4
    · exact s63_5_5
    · exact s63_5_6
    · exact s63_5_7
  · exact List.all_eq_true.mp col63_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col63_7 v (List.mem_finRange v)
theorem col64_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 0 v) = true := by decide +kernel
theorem col64_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 1 v) = true := by decide +kernel
theorem s64_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 0 = true := by decide +kernel
theorem s64_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 1 = true := by decide +kernel
theorem s64_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 2 = true := by decide +kernel
theorem s64_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 3 = true := by decide +kernel
theorem k64_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k64_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k64_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s64_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k64_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k64_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k64_2_4_80 k h.1 (by omega)
theorem s64_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 5 = true := by decide +kernel
theorem s64_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 6 = true := by decide +kernel
theorem s64_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 2 7 = true := by decide +kernel
theorem s64_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 0 = true := by decide +kernel
theorem s64_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 1 = true := by decide +kernel
theorem s64_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 2 = true := by decide +kernel
theorem s64_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 3 = true := by decide +kernel
theorem k64_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k64_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k64_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s64_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k64_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k64_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 64) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (64 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k64_3_4_80 k h.1 (by omega)
theorem s64_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 5 = true := by decide +kernel
theorem s64_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 6 = true := by decide +kernel
theorem s64_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 3 7 = true := by decide +kernel
theorem s64_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 0 = true := by decide +kernel
theorem s64_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 1 = true := by decide +kernel
theorem s64_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 2 = true := by decide +kernel
theorem s64_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 3 = true := by decide +kernel
theorem s64_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 4 = true := by decide +kernel
theorem k64_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k64_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k64_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k64_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k64_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k64_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k64_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k64_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k64_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s64_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k64_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k64_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k64_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k64_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k64_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k64_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k64_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k64_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 5).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k64_4_5_40 k h.1 (by omega)
theorem k64_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k64_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k64_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k64_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k64_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k64_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k64_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k64_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k64_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k64_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k64_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s64_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k64_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k64_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k64_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k64_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k64_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k64_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k64_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k64_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k64_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k64_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 4 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k64_4_6_50 k h.1 (by omega)
theorem s64_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 4 7 = true := by decide +kernel
theorem s64_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 0 = true := by decide +kernel
theorem s64_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 1 = true := by decide +kernel
theorem s64_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 2 = true := by decide +kernel
theorem s64_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 3 = true := by decide +kernel
theorem s64_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 4 = true := by decide +kernel
theorem s64_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 5 = true := by decide +kernel
theorem k64_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k64_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k64_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k64_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k64_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k64_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s64_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k64_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k64_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k64_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k64_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k64_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 64) ((InDA2.TCasaD 4 5 6).getD (64 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k64_5_6_50 k h.1 (by omega)
theorem s64_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 5 7 = true := by decide +kernel
theorem col64_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 6 v) = true := by decide +kernel
theorem col64_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 7 v) = true := by decide +kernel
theorem col64 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 64) 64 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col64_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col64_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s64_2_0
    · exact s64_2_1
    · exact s64_2_2
    · exact s64_2_3
    · exact s64_2_4
    · exact s64_2_5
    · exact s64_2_6
    · exact s64_2_7
  · fin_cases v
    · exact s64_3_0
    · exact s64_3_1
    · exact s64_3_2
    · exact s64_3_3
    · exact s64_3_4
    · exact s64_3_5
    · exact s64_3_6
    · exact s64_3_7
  · fin_cases v
    · exact s64_4_0
    · exact s64_4_1
    · exact s64_4_2
    · exact s64_4_3
    · exact s64_4_4
    · exact s64_4_5
    · exact s64_4_6
    · exact s64_4_7
  · fin_cases v
    · exact s64_5_0
    · exact s64_5_1
    · exact s64_5_2
    · exact s64_5_3
    · exact s64_5_4
    · exact s64_5_5
    · exact s64_5_6
    · exact s64_5_7
  · exact List.all_eq_true.mp col64_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col64_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
