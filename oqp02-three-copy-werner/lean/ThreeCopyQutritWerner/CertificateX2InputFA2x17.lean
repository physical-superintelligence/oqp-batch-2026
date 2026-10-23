module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [85, 90). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col85_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 0 v) = true := by decide +kernel
theorem col85_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 1 v) = true := by decide +kernel
theorem s85_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 0 = true := by decide +kernel
theorem s85_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 1 = true := by decide +kernel
theorem s85_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 2 = true := by decide +kernel
theorem s85_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 3 = true := by decide +kernel
theorem k85_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k85_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k85_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s85_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k85_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k85_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k85_2_4_80 k h.1 (by omega)
theorem s85_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 5 = true := by decide +kernel
theorem s85_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 6 = true := by decide +kernel
theorem s85_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 2 7 = true := by decide +kernel
theorem s85_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 0 = true := by decide +kernel
theorem s85_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 1 = true := by decide +kernel
theorem s85_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 2 = true := by decide +kernel
theorem s85_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 3 = true := by decide +kernel
theorem k85_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k85_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k85_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s85_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k85_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k85_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 85) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (85 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k85_3_4_80 k h.1 (by omega)
theorem s85_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 5 = true := by decide +kernel
theorem s85_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 6 = true := by decide +kernel
theorem s85_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 3 7 = true := by decide +kernel
theorem s85_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 0 = true := by decide +kernel
theorem s85_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 1 = true := by decide +kernel
theorem s85_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 2 = true := by decide +kernel
theorem s85_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 3 = true := by decide +kernel
theorem s85_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 4 = true := by decide +kernel
theorem k85_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k85_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k85_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k85_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k85_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k85_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k85_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k85_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k85_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s85_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k85_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k85_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k85_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k85_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k85_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k85_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k85_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k85_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 5).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k85_4_5_40 k h.1 (by omega)
theorem k85_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k85_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k85_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k85_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k85_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k85_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k85_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k85_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k85_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k85_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k85_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s85_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k85_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k85_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k85_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k85_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k85_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k85_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k85_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k85_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k85_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k85_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 4 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k85_4_6_50 k h.1 (by omega)
theorem s85_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 4 7 = true := by decide +kernel
theorem s85_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 0 = true := by decide +kernel
theorem s85_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 1 = true := by decide +kernel
theorem s85_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 2 = true := by decide +kernel
theorem s85_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 3 = true := by decide +kernel
theorem s85_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 4 = true := by decide +kernel
theorem s85_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 5 = true := by decide +kernel
theorem k85_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k85_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k85_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k85_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k85_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k85_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s85_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k85_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k85_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k85_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k85_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k85_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 85) ((InDA2.TCasaD 4 5 6).getD (85 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k85_5_6_50 k h.1 (by omega)
theorem s85_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 5 7 = true := by decide +kernel
theorem col85_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 6 v) = true := by decide +kernel
theorem col85_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 7 v) = true := by decide +kernel
theorem col85 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 85) 85 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col85_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col85_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s85_2_0
    · exact s85_2_1
    · exact s85_2_2
    · exact s85_2_3
    · exact s85_2_4
    · exact s85_2_5
    · exact s85_2_6
    · exact s85_2_7
  · fin_cases v
    · exact s85_3_0
    · exact s85_3_1
    · exact s85_3_2
    · exact s85_3_3
    · exact s85_3_4
    · exact s85_3_5
    · exact s85_3_6
    · exact s85_3_7
  · fin_cases v
    · exact s85_4_0
    · exact s85_4_1
    · exact s85_4_2
    · exact s85_4_3
    · exact s85_4_4
    · exact s85_4_5
    · exact s85_4_6
    · exact s85_4_7
  · fin_cases v
    · exact s85_5_0
    · exact s85_5_1
    · exact s85_5_2
    · exact s85_5_3
    · exact s85_5_4
    · exact s85_5_5
    · exact s85_5_6
    · exact s85_5_7
  · exact List.all_eq_true.mp col85_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col85_7 v (List.mem_finRange v)
theorem col86_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 0 v) = true := by decide +kernel
theorem col86_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 1 v) = true := by decide +kernel
theorem s86_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 0 = true := by decide +kernel
theorem s86_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 1 = true := by decide +kernel
theorem s86_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 2 = true := by decide +kernel
theorem s86_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 3 = true := by decide +kernel
theorem k86_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k86_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k86_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s86_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k86_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k86_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k86_2_4_80 k h.1 (by omega)
theorem s86_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 5 = true := by decide +kernel
theorem s86_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 6 = true := by decide +kernel
theorem s86_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 2 7 = true := by decide +kernel
theorem s86_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 0 = true := by decide +kernel
theorem s86_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 1 = true := by decide +kernel
theorem s86_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 2 = true := by decide +kernel
theorem s86_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 3 = true := by decide +kernel
theorem k86_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k86_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k86_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s86_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k86_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k86_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 86) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (86 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k86_3_4_80 k h.1 (by omega)
theorem s86_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 5 = true := by decide +kernel
theorem s86_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 6 = true := by decide +kernel
theorem s86_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 3 7 = true := by decide +kernel
theorem s86_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 0 = true := by decide +kernel
theorem s86_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 1 = true := by decide +kernel
theorem s86_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 2 = true := by decide +kernel
theorem s86_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 3 = true := by decide +kernel
theorem s86_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 4 = true := by decide +kernel
theorem k86_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k86_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k86_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k86_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k86_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k86_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k86_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k86_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k86_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s86_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k86_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k86_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k86_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k86_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k86_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k86_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k86_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k86_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 5).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k86_4_5_40 k h.1 (by omega)
theorem k86_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k86_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k86_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k86_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k86_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k86_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k86_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k86_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k86_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k86_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k86_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s86_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k86_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k86_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k86_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k86_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k86_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k86_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k86_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k86_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k86_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k86_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 4 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k86_4_6_50 k h.1 (by omega)
theorem s86_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 4 7 = true := by decide +kernel
theorem s86_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 0 = true := by decide +kernel
theorem s86_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 1 = true := by decide +kernel
theorem s86_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 2 = true := by decide +kernel
theorem s86_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 3 = true := by decide +kernel
theorem s86_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 4 = true := by decide +kernel
theorem s86_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 5 = true := by decide +kernel
theorem k86_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k86_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k86_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k86_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k86_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k86_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s86_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k86_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k86_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k86_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k86_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k86_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 86) ((InDA2.TCasaD 4 5 6).getD (86 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k86_5_6_50 k h.1 (by omega)
theorem s86_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 5 7 = true := by decide +kernel
theorem col86_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 6 v) = true := by decide +kernel
theorem col86_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 7 v) = true := by decide +kernel
theorem col86 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 86) 86 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col86_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col86_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s86_2_0
    · exact s86_2_1
    · exact s86_2_2
    · exact s86_2_3
    · exact s86_2_4
    · exact s86_2_5
    · exact s86_2_6
    · exact s86_2_7
  · fin_cases v
    · exact s86_3_0
    · exact s86_3_1
    · exact s86_3_2
    · exact s86_3_3
    · exact s86_3_4
    · exact s86_3_5
    · exact s86_3_6
    · exact s86_3_7
  · fin_cases v
    · exact s86_4_0
    · exact s86_4_1
    · exact s86_4_2
    · exact s86_4_3
    · exact s86_4_4
    · exact s86_4_5
    · exact s86_4_6
    · exact s86_4_7
  · fin_cases v
    · exact s86_5_0
    · exact s86_5_1
    · exact s86_5_2
    · exact s86_5_3
    · exact s86_5_4
    · exact s86_5_5
    · exact s86_5_6
    · exact s86_5_7
  · exact List.all_eq_true.mp col86_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col86_7 v (List.mem_finRange v)
theorem col87_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 0 v) = true := by decide +kernel
theorem col87_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 1 v) = true := by decide +kernel
theorem s87_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 0 = true := by decide +kernel
theorem s87_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 1 = true := by decide +kernel
theorem s87_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 2 = true := by decide +kernel
theorem s87_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 3 = true := by decide +kernel
theorem k87_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k87_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k87_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s87_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k87_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k87_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k87_2_4_80 k h.1 (by omega)
theorem s87_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 5 = true := by decide +kernel
theorem s87_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 6 = true := by decide +kernel
theorem s87_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 2 7 = true := by decide +kernel
theorem s87_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 0 = true := by decide +kernel
theorem s87_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 1 = true := by decide +kernel
theorem s87_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 2 = true := by decide +kernel
theorem s87_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 3 = true := by decide +kernel
theorem k87_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k87_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k87_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s87_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k87_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k87_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 87) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (87 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k87_3_4_80 k h.1 (by omega)
theorem s87_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 5 = true := by decide +kernel
theorem s87_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 6 = true := by decide +kernel
theorem s87_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 3 7 = true := by decide +kernel
theorem s87_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 0 = true := by decide +kernel
theorem s87_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 1 = true := by decide +kernel
theorem s87_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 2 = true := by decide +kernel
theorem s87_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 3 = true := by decide +kernel
theorem s87_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 4 = true := by decide +kernel
theorem k87_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k87_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k87_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k87_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k87_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k87_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k87_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k87_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k87_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s87_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k87_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k87_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k87_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k87_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k87_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k87_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k87_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k87_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 5).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k87_4_5_40 k h.1 (by omega)
theorem k87_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k87_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k87_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k87_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k87_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k87_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k87_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k87_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k87_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k87_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k87_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s87_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k87_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k87_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k87_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k87_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k87_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k87_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k87_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k87_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k87_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k87_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 4 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k87_4_6_50 k h.1 (by omega)
theorem s87_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 4 7 = true := by decide +kernel
theorem s87_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 0 = true := by decide +kernel
theorem s87_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 1 = true := by decide +kernel
theorem s87_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 2 = true := by decide +kernel
theorem s87_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 3 = true := by decide +kernel
theorem s87_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 4 = true := by decide +kernel
theorem s87_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 5 = true := by decide +kernel
theorem k87_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k87_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k87_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k87_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k87_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k87_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s87_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k87_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k87_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k87_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k87_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k87_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 87) ((InDA2.TCasaD 4 5 6).getD (87 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k87_5_6_50 k h.1 (by omega)
theorem s87_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 5 7 = true := by decide +kernel
theorem col87_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 6 v) = true := by decide +kernel
theorem col87_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 7 v) = true := by decide +kernel
theorem col87 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 87) 87 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col87_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col87_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s87_2_0
    · exact s87_2_1
    · exact s87_2_2
    · exact s87_2_3
    · exact s87_2_4
    · exact s87_2_5
    · exact s87_2_6
    · exact s87_2_7
  · fin_cases v
    · exact s87_3_0
    · exact s87_3_1
    · exact s87_3_2
    · exact s87_3_3
    · exact s87_3_4
    · exact s87_3_5
    · exact s87_3_6
    · exact s87_3_7
  · fin_cases v
    · exact s87_4_0
    · exact s87_4_1
    · exact s87_4_2
    · exact s87_4_3
    · exact s87_4_4
    · exact s87_4_5
    · exact s87_4_6
    · exact s87_4_7
  · fin_cases v
    · exact s87_5_0
    · exact s87_5_1
    · exact s87_5_2
    · exact s87_5_3
    · exact s87_5_4
    · exact s87_5_5
    · exact s87_5_6
    · exact s87_5_7
  · exact List.all_eq_true.mp col87_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col87_7 v (List.mem_finRange v)
theorem col88_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 0 v) = true := by decide +kernel
theorem col88_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 1 v) = true := by decide +kernel
theorem s88_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 0 = true := by decide +kernel
theorem s88_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 1 = true := by decide +kernel
theorem s88_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 2 = true := by decide +kernel
theorem s88_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 3 = true := by decide +kernel
theorem k88_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k88_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k88_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s88_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k88_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k88_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k88_2_4_80 k h.1 (by omega)
theorem s88_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 5 = true := by decide +kernel
theorem s88_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 6 = true := by decide +kernel
theorem s88_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 2 7 = true := by decide +kernel
theorem s88_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 0 = true := by decide +kernel
theorem s88_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 1 = true := by decide +kernel
theorem s88_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 2 = true := by decide +kernel
theorem s88_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 3 = true := by decide +kernel
theorem k88_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k88_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k88_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s88_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k88_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k88_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 88) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (88 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k88_3_4_80 k h.1 (by omega)
theorem s88_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 5 = true := by decide +kernel
theorem s88_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 6 = true := by decide +kernel
theorem s88_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 3 7 = true := by decide +kernel
theorem s88_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 0 = true := by decide +kernel
theorem s88_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 1 = true := by decide +kernel
theorem s88_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 2 = true := by decide +kernel
theorem s88_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 3 = true := by decide +kernel
theorem s88_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 4 = true := by decide +kernel
theorem k88_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k88_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k88_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k88_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k88_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k88_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k88_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k88_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k88_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s88_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k88_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k88_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k88_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k88_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k88_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k88_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k88_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k88_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 5).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k88_4_5_40 k h.1 (by omega)
theorem k88_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k88_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k88_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k88_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k88_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k88_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k88_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k88_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k88_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k88_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k88_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s88_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k88_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k88_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k88_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k88_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k88_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k88_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k88_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k88_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k88_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k88_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 4 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k88_4_6_50 k h.1 (by omega)
theorem s88_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 4 7 = true := by decide +kernel
theorem s88_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 0 = true := by decide +kernel
theorem s88_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 1 = true := by decide +kernel
theorem s88_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 2 = true := by decide +kernel
theorem s88_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 3 = true := by decide +kernel
theorem s88_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 4 = true := by decide +kernel
theorem s88_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 5 = true := by decide +kernel
theorem k88_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k88_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k88_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k88_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k88_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k88_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s88_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k88_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k88_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k88_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k88_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k88_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 88) ((InDA2.TCasaD 4 5 6).getD (88 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k88_5_6_50 k h.1 (by omega)
theorem s88_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 5 7 = true := by decide +kernel
theorem col88_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 6 v) = true := by decide +kernel
theorem col88_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 7 v) = true := by decide +kernel
theorem col88 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 88) 88 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col88_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col88_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s88_2_0
    · exact s88_2_1
    · exact s88_2_2
    · exact s88_2_3
    · exact s88_2_4
    · exact s88_2_5
    · exact s88_2_6
    · exact s88_2_7
  · fin_cases v
    · exact s88_3_0
    · exact s88_3_1
    · exact s88_3_2
    · exact s88_3_3
    · exact s88_3_4
    · exact s88_3_5
    · exact s88_3_6
    · exact s88_3_7
  · fin_cases v
    · exact s88_4_0
    · exact s88_4_1
    · exact s88_4_2
    · exact s88_4_3
    · exact s88_4_4
    · exact s88_4_5
    · exact s88_4_6
    · exact s88_4_7
  · fin_cases v
    · exact s88_5_0
    · exact s88_5_1
    · exact s88_5_2
    · exact s88_5_3
    · exact s88_5_4
    · exact s88_5_5
    · exact s88_5_6
    · exact s88_5_7
  · exact List.all_eq_true.mp col88_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col88_7 v (List.mem_finRange v)
theorem col89_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 0 v) = true := by decide +kernel
theorem col89_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 1 v) = true := by decide +kernel
theorem s89_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 0 = true := by decide +kernel
theorem s89_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 1 = true := by decide +kernel
theorem s89_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 2 = true := by decide +kernel
theorem s89_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 3 = true := by decide +kernel
theorem k89_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k89_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k89_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s89_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k89_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k89_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k89_2_4_80 k h.1 (by omega)
theorem s89_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 5 = true := by decide +kernel
theorem s89_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 6 = true := by decide +kernel
theorem s89_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 2 7 = true := by decide +kernel
theorem s89_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 0 = true := by decide +kernel
theorem s89_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 1 = true := by decide +kernel
theorem s89_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 2 = true := by decide +kernel
theorem s89_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 3 = true := by decide +kernel
theorem k89_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k89_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k89_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s89_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k89_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k89_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 89) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (89 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k89_3_4_80 k h.1 (by omega)
theorem s89_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 5 = true := by decide +kernel
theorem s89_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 6 = true := by decide +kernel
theorem s89_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 3 7 = true := by decide +kernel
theorem s89_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 0 = true := by decide +kernel
theorem s89_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 1 = true := by decide +kernel
theorem s89_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 2 = true := by decide +kernel
theorem s89_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 3 = true := by decide +kernel
theorem s89_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 4 = true := by decide +kernel
theorem k89_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k89_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k89_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k89_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k89_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k89_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k89_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k89_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k89_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s89_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k89_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k89_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k89_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k89_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k89_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k89_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k89_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k89_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 5).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k89_4_5_40 k h.1 (by omega)
theorem k89_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k89_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k89_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k89_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k89_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k89_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k89_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k89_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k89_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k89_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k89_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s89_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k89_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k89_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k89_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k89_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k89_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k89_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k89_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k89_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k89_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k89_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 4 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k89_4_6_50 k h.1 (by omega)
theorem s89_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 4 7 = true := by decide +kernel
theorem s89_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 0 = true := by decide +kernel
theorem s89_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 1 = true := by decide +kernel
theorem s89_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 2 = true := by decide +kernel
theorem s89_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 3 = true := by decide +kernel
theorem s89_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 4 = true := by decide +kernel
theorem s89_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 5 = true := by decide +kernel
theorem k89_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k89_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k89_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k89_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k89_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k89_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s89_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k89_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k89_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k89_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k89_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k89_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 89) ((InDA2.TCasaD 4 5 6).getD (89 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k89_5_6_50 k h.1 (by omega)
theorem s89_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 5 7 = true := by decide +kernel
theorem col89_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 6 v) = true := by decide +kernel
theorem col89_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 7 v) = true := by decide +kernel
theorem col89 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 89) 89 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col89_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col89_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s89_2_0
    · exact s89_2_1
    · exact s89_2_2
    · exact s89_2_3
    · exact s89_2_4
    · exact s89_2_5
    · exact s89_2_6
    · exact s89_2_7
  · fin_cases v
    · exact s89_3_0
    · exact s89_3_1
    · exact s89_3_2
    · exact s89_3_3
    · exact s89_3_4
    · exact s89_3_5
    · exact s89_3_6
    · exact s89_3_7
  · fin_cases v
    · exact s89_4_0
    · exact s89_4_1
    · exact s89_4_2
    · exact s89_4_3
    · exact s89_4_4
    · exact s89_4_5
    · exact s89_4_6
    · exact s89_4_7
  · fin_cases v
    · exact s89_5_0
    · exact s89_5_1
    · exact s89_5_2
    · exact s89_5_3
    · exact s89_5_4
    · exact s89_5_5
    · exact s89_5_6
    · exact s89_5_7
  · exact List.all_eq_true.mp col89_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col89_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
