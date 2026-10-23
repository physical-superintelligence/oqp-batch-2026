module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [130, 135). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col130_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 0 v) = true := by decide +kernel
theorem col130_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 1 v) = true := by decide +kernel
theorem s130_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 0 = true := by decide +kernel
theorem s130_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 1 = true := by decide +kernel
theorem s130_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 2 = true := by decide +kernel
theorem s130_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 3 = true := by decide +kernel
theorem k130_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k130_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k130_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s130_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k130_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k130_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 2 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k130_2_4_80 k h.1 (by omega)
theorem s130_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 5 = true := by decide +kernel
theorem s130_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 6 = true := by decide +kernel
theorem s130_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 2 7 = true := by decide +kernel
theorem s130_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 0 = true := by decide +kernel
theorem s130_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 1 = true := by decide +kernel
theorem s130_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 2 = true := by decide +kernel
theorem s130_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 3 = true := by decide +kernel
theorem k130_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k130_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k130_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s130_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 4 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k130_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k130_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 130) (InDA2.TTsaaD 3 4 4) (posA (x2Mult 2 4) (130 - x2AOff 2 4)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k130_3_4_80 k h.1 (by omega)
theorem s130_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 5 = true := by decide +kernel
theorem s130_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 6 = true := by decide +kernel
theorem s130_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 3 7 = true := by decide +kernel
theorem s130_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 0 = true := by decide +kernel
theorem s130_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 1 = true := by decide +kernel
theorem s130_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 2 = true := by decide +kernel
theorem s130_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 3 = true := by decide +kernel
theorem s130_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 4 = true := by decide +kernel
theorem k130_4_5_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k130_4_5_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k130_4_5_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k130_4_5_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k130_4_5_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k130_4_5_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k130_4_5_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k130_4_5_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k130_4_5_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s130_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 5 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k130_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k130_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k130_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k130_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k130_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k130_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k130_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k130_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 5).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k130_4_5_40 k h.1 (by omega)
theorem k130_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k130_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k130_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k130_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k130_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k130_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k130_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k130_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k130_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k130_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k130_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s130_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k130_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k130_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k130_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k130_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k130_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k130_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k130_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k130_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k130_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k130_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 4 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k130_4_6_50 k h.1 (by omega)
theorem s130_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 4 7 = true := by decide +kernel
theorem s130_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 0 = true := by decide +kernel
theorem s130_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 1 = true := by decide +kernel
theorem s130_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 2 = true := by decide +kernel
theorem s130_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 3 = true := by decide +kernel
theorem s130_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 4 = true := by decide +kernel
theorem s130_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 5 = true := by decide +kernel
theorem k130_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k130_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k130_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k130_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k130_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k130_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s130_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k130_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k130_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k130_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k130_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k130_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 130) ((InDA2.TCasaD 4 5 6).getD (130 - x2AOff 2 4) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k130_5_6_50 k h.1 (by omega)
theorem s130_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 5 7 = true := by decide +kernel
theorem col130_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 6 v) = true := by decide +kernel
theorem col130_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 7 v) = true := by decide +kernel
theorem col130 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 130) 130 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col130_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col130_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s130_2_0
    · exact s130_2_1
    · exact s130_2_2
    · exact s130_2_3
    · exact s130_2_4
    · exact s130_2_5
    · exact s130_2_6
    · exact s130_2_7
  · fin_cases v
    · exact s130_3_0
    · exact s130_3_1
    · exact s130_3_2
    · exact s130_3_3
    · exact s130_3_4
    · exact s130_3_5
    · exact s130_3_6
    · exact s130_3_7
  · fin_cases v
    · exact s130_4_0
    · exact s130_4_1
    · exact s130_4_2
    · exact s130_4_3
    · exact s130_4_4
    · exact s130_4_5
    · exact s130_4_6
    · exact s130_4_7
  · fin_cases v
    · exact s130_5_0
    · exact s130_5_1
    · exact s130_5_2
    · exact s130_5_3
    · exact s130_5_4
    · exact s130_5_5
    · exact s130_5_6
    · exact s130_5_7
  · exact List.all_eq_true.mp col130_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col130_7 v (List.mem_finRange v)
theorem col131_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 0 v) = true := by decide +kernel
theorem col131_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 1 v) = true := by decide +kernel
theorem s131_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 0 = true := by decide +kernel
theorem s131_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 1 = true := by decide +kernel
theorem s131_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 2 = true := by decide +kernel
theorem s131_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 3 = true := by decide +kernel
theorem k131_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k131_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k131_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s131_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k131_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k131_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k131_2_4_80 k h.1 (by omega)
theorem s131_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 5 = true := by decide +kernel
theorem s131_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 6 = true := by decide +kernel
theorem s131_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 2 7 = true := by decide +kernel
theorem s131_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 0 = true := by decide +kernel
theorem s131_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 1 = true := by decide +kernel
theorem s131_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 2 = true := by decide +kernel
theorem s131_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 3 = true := by decide +kernel
theorem k131_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k131_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k131_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s131_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k131_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k131_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k131_3_4_80 k h.1 (by omega)
theorem s131_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 5 = true := by decide +kernel
theorem s131_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 6 = true := by decide +kernel
theorem s131_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 3 7 = true := by decide +kernel
theorem s131_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 0 = true := by decide +kernel
theorem s131_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 1 = true := by decide +kernel
theorem s131_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 2 = true := by decide +kernel
theorem s131_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 3 = true := by decide +kernel
theorem k131_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k131_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k131_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k131_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k131_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k131_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k131_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k131_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k131_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k131_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k131_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k131_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k131_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k131_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k131_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k131_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k131_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k131_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k131_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k131_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k131_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s131_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k131_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k131_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k131_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k131_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k131_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k131_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k131_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k131_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k131_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k131_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k131_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k131_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k131_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k131_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k131_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k131_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k131_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k131_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k131_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k131_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k131_4_4_100 k h.1 (by omega)
theorem k131_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k131_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k131_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k131_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k131_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k131_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k131_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k131_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k131_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s131_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k131_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k131_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k131_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k131_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k131_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k131_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k131_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k131_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 131) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (131 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k131_4_5_40 k h.1 (by omega)
theorem k131_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k131_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k131_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k131_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k131_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k131_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k131_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k131_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k131_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k131_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k131_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s131_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k131_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k131_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k131_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k131_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k131_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k131_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k131_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k131_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k131_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k131_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TTsaaD 4 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k131_4_6_50 k h.1 (by omega)
theorem s131_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 4 7 = true := by decide +kernel
theorem s131_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 0 = true := by decide +kernel
theorem s131_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 1 = true := by decide +kernel
theorem s131_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 2 = true := by decide +kernel
theorem s131_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 3 = true := by decide +kernel
theorem s131_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 4 = true := by decide +kernel
theorem s131_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 5 = true := by decide +kernel
theorem k131_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k131_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k131_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k131_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k131_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k131_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s131_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k131_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k131_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k131_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k131_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k131_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 131) ((InDA2.TCasaD 5 5 6).getD (131 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k131_5_6_50 k h.1 (by omega)
theorem s131_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 5 7 = true := by decide +kernel
theorem col131_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 6 v) = true := by decide +kernel
theorem col131_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 7 v) = true := by decide +kernel
theorem col131 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 131) 131 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col131_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col131_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s131_2_0
    · exact s131_2_1
    · exact s131_2_2
    · exact s131_2_3
    · exact s131_2_4
    · exact s131_2_5
    · exact s131_2_6
    · exact s131_2_7
  · fin_cases v
    · exact s131_3_0
    · exact s131_3_1
    · exact s131_3_2
    · exact s131_3_3
    · exact s131_3_4
    · exact s131_3_5
    · exact s131_3_6
    · exact s131_3_7
  · fin_cases v
    · exact s131_4_0
    · exact s131_4_1
    · exact s131_4_2
    · exact s131_4_3
    · exact s131_4_4
    · exact s131_4_5
    · exact s131_4_6
    · exact s131_4_7
  · fin_cases v
    · exact s131_5_0
    · exact s131_5_1
    · exact s131_5_2
    · exact s131_5_3
    · exact s131_5_4
    · exact s131_5_5
    · exact s131_5_6
    · exact s131_5_7
  · exact List.all_eq_true.mp col131_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col131_7 v (List.mem_finRange v)
theorem col132_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 0 v) = true := by decide +kernel
theorem col132_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 1 v) = true := by decide +kernel
theorem s132_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 0 = true := by decide +kernel
theorem s132_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 1 = true := by decide +kernel
theorem s132_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 2 = true := by decide +kernel
theorem s132_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 3 = true := by decide +kernel
theorem k132_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k132_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k132_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s132_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k132_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k132_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k132_2_4_80 k h.1 (by omega)
theorem s132_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 5 = true := by decide +kernel
theorem s132_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 6 = true := by decide +kernel
theorem s132_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 2 7 = true := by decide +kernel
theorem s132_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 0 = true := by decide +kernel
theorem s132_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 1 = true := by decide +kernel
theorem s132_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 2 = true := by decide +kernel
theorem s132_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 3 = true := by decide +kernel
theorem k132_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k132_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k132_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s132_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k132_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k132_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k132_3_4_80 k h.1 (by omega)
theorem s132_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 5 = true := by decide +kernel
theorem s132_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 6 = true := by decide +kernel
theorem s132_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 3 7 = true := by decide +kernel
theorem s132_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 0 = true := by decide +kernel
theorem s132_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 1 = true := by decide +kernel
theorem s132_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 2 = true := by decide +kernel
theorem s132_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 3 = true := by decide +kernel
theorem k132_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k132_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k132_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k132_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k132_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k132_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k132_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k132_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k132_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k132_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k132_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k132_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k132_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k132_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k132_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k132_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k132_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k132_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k132_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k132_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k132_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s132_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k132_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k132_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k132_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k132_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k132_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k132_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k132_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k132_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k132_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k132_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k132_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k132_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k132_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k132_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k132_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k132_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k132_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k132_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k132_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k132_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k132_4_4_100 k h.1 (by omega)
theorem k132_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k132_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k132_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k132_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k132_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k132_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k132_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k132_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k132_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s132_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k132_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k132_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k132_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k132_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k132_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k132_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k132_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k132_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 132) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (132 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k132_4_5_40 k h.1 (by omega)
theorem k132_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k132_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k132_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k132_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k132_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k132_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k132_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k132_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k132_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k132_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k132_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s132_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k132_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k132_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k132_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k132_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k132_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k132_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k132_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k132_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k132_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k132_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TTsaaD 4 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k132_4_6_50 k h.1 (by omega)
theorem s132_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 4 7 = true := by decide +kernel
theorem s132_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 0 = true := by decide +kernel
theorem s132_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 1 = true := by decide +kernel
theorem s132_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 2 = true := by decide +kernel
theorem s132_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 3 = true := by decide +kernel
theorem s132_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 4 = true := by decide +kernel
theorem s132_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 5 = true := by decide +kernel
theorem k132_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k132_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k132_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k132_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k132_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k132_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s132_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k132_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k132_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k132_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k132_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k132_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 132) ((InDA2.TCasaD 5 5 6).getD (132 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k132_5_6_50 k h.1 (by omega)
theorem s132_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 5 7 = true := by decide +kernel
theorem col132_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 6 v) = true := by decide +kernel
theorem col132_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 7 v) = true := by decide +kernel
theorem col132 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 132) 132 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col132_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col132_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s132_2_0
    · exact s132_2_1
    · exact s132_2_2
    · exact s132_2_3
    · exact s132_2_4
    · exact s132_2_5
    · exact s132_2_6
    · exact s132_2_7
  · fin_cases v
    · exact s132_3_0
    · exact s132_3_1
    · exact s132_3_2
    · exact s132_3_3
    · exact s132_3_4
    · exact s132_3_5
    · exact s132_3_6
    · exact s132_3_7
  · fin_cases v
    · exact s132_4_0
    · exact s132_4_1
    · exact s132_4_2
    · exact s132_4_3
    · exact s132_4_4
    · exact s132_4_5
    · exact s132_4_6
    · exact s132_4_7
  · fin_cases v
    · exact s132_5_0
    · exact s132_5_1
    · exact s132_5_2
    · exact s132_5_3
    · exact s132_5_4
    · exact s132_5_5
    · exact s132_5_6
    · exact s132_5_7
  · exact List.all_eq_true.mp col132_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col132_7 v (List.mem_finRange v)
theorem col133_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 0 v) = true := by decide +kernel
theorem col133_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 1 v) = true := by decide +kernel
theorem s133_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 0 = true := by decide +kernel
theorem s133_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 1 = true := by decide +kernel
theorem s133_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 2 = true := by decide +kernel
theorem s133_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 3 = true := by decide +kernel
theorem k133_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k133_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k133_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s133_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k133_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k133_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k133_2_4_80 k h.1 (by omega)
theorem s133_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 5 = true := by decide +kernel
theorem s133_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 6 = true := by decide +kernel
theorem s133_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 2 7 = true := by decide +kernel
theorem s133_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 0 = true := by decide +kernel
theorem s133_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 1 = true := by decide +kernel
theorem s133_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 2 = true := by decide +kernel
theorem s133_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 3 = true := by decide +kernel
theorem k133_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k133_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k133_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s133_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k133_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k133_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k133_3_4_80 k h.1 (by omega)
theorem s133_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 5 = true := by decide +kernel
theorem s133_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 6 = true := by decide +kernel
theorem s133_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 3 7 = true := by decide +kernel
theorem s133_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 0 = true := by decide +kernel
theorem s133_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 1 = true := by decide +kernel
theorem s133_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 2 = true := by decide +kernel
theorem s133_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 3 = true := by decide +kernel
theorem k133_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k133_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k133_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k133_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k133_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k133_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k133_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k133_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k133_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k133_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k133_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k133_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k133_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k133_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k133_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k133_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k133_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k133_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k133_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k133_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k133_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s133_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k133_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k133_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k133_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k133_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k133_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k133_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k133_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k133_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k133_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k133_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k133_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k133_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k133_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k133_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k133_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k133_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k133_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k133_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k133_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k133_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k133_4_4_100 k h.1 (by omega)
theorem k133_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k133_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k133_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k133_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k133_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k133_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k133_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k133_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k133_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s133_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k133_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k133_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k133_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k133_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k133_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k133_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k133_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k133_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 133) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (133 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k133_4_5_40 k h.1 (by omega)
theorem k133_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k133_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k133_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k133_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k133_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k133_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k133_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k133_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k133_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k133_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k133_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s133_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k133_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k133_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k133_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k133_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k133_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k133_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k133_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k133_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k133_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k133_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TTsaaD 4 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k133_4_6_50 k h.1 (by omega)
theorem s133_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 4 7 = true := by decide +kernel
theorem s133_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 0 = true := by decide +kernel
theorem s133_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 1 = true := by decide +kernel
theorem s133_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 2 = true := by decide +kernel
theorem s133_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 3 = true := by decide +kernel
theorem s133_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 4 = true := by decide +kernel
theorem s133_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 5 = true := by decide +kernel
theorem k133_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k133_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k133_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k133_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k133_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k133_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s133_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k133_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k133_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k133_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k133_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k133_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 133) ((InDA2.TCasaD 5 5 6).getD (133 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k133_5_6_50 k h.1 (by omega)
theorem s133_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 5 7 = true := by decide +kernel
theorem col133_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 6 v) = true := by decide +kernel
theorem col133_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 7 v) = true := by decide +kernel
theorem col133 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 133) 133 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col133_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col133_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s133_2_0
    · exact s133_2_1
    · exact s133_2_2
    · exact s133_2_3
    · exact s133_2_4
    · exact s133_2_5
    · exact s133_2_6
    · exact s133_2_7
  · fin_cases v
    · exact s133_3_0
    · exact s133_3_1
    · exact s133_3_2
    · exact s133_3_3
    · exact s133_3_4
    · exact s133_3_5
    · exact s133_3_6
    · exact s133_3_7
  · fin_cases v
    · exact s133_4_0
    · exact s133_4_1
    · exact s133_4_2
    · exact s133_4_3
    · exact s133_4_4
    · exact s133_4_5
    · exact s133_4_6
    · exact s133_4_7
  · fin_cases v
    · exact s133_5_0
    · exact s133_5_1
    · exact s133_5_2
    · exact s133_5_3
    · exact s133_5_4
    · exact s133_5_5
    · exact s133_5_6
    · exact s133_5_7
  · exact List.all_eq_true.mp col133_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col133_7 v (List.mem_finRange v)
theorem col134_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 0 v) = true := by decide +kernel
theorem col134_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 1 v) = true := by decide +kernel
theorem s134_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 0 = true := by decide +kernel
theorem s134_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 1 = true := by decide +kernel
theorem s134_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 2 = true := by decide +kernel
theorem s134_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 3 = true := by decide +kernel
theorem k134_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k134_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k134_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s134_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k134_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k134_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k134_2_4_80 k h.1 (by omega)
theorem s134_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 5 = true := by decide +kernel
theorem s134_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 6 = true := by decide +kernel
theorem s134_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 2 7 = true := by decide +kernel
theorem s134_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 0 = true := by decide +kernel
theorem s134_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 1 = true := by decide +kernel
theorem s134_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 2 = true := by decide +kernel
theorem s134_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 3 = true := by decide +kernel
theorem k134_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k134_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k134_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s134_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k134_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k134_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k134_3_4_80 k h.1 (by omega)
theorem s134_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 5 = true := by decide +kernel
theorem s134_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 6 = true := by decide +kernel
theorem s134_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 3 7 = true := by decide +kernel
theorem s134_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 0 = true := by decide +kernel
theorem s134_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 1 = true := by decide +kernel
theorem s134_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 2 = true := by decide +kernel
theorem s134_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 3 = true := by decide +kernel
theorem k134_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k134_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k134_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k134_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k134_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k134_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k134_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k134_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k134_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k134_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k134_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k134_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k134_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k134_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k134_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k134_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k134_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k134_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k134_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k134_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k134_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s134_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k134_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k134_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k134_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k134_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k134_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k134_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k134_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k134_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k134_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k134_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k134_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k134_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k134_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k134_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k134_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k134_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k134_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k134_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k134_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k134_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k134_4_4_100 k h.1 (by omega)
theorem k134_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k134_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k134_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k134_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k134_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k134_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k134_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k134_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k134_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s134_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k134_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k134_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k134_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k134_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k134_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k134_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k134_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k134_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 134) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (134 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k134_4_5_40 k h.1 (by omega)
theorem k134_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k134_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k134_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k134_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k134_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k134_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k134_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k134_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k134_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k134_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k134_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s134_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k134_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k134_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k134_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k134_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k134_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k134_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k134_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k134_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k134_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k134_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TTsaaD 4 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k134_4_6_50 k h.1 (by omega)
theorem s134_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 4 7 = true := by decide +kernel
theorem s134_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 0 = true := by decide +kernel
theorem s134_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 1 = true := by decide +kernel
theorem s134_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 2 = true := by decide +kernel
theorem s134_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 3 = true := by decide +kernel
theorem s134_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 4 = true := by decide +kernel
theorem s134_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 5 = true := by decide +kernel
theorem k134_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k134_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k134_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k134_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k134_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k134_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s134_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k134_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k134_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k134_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k134_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k134_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 134) ((InDA2.TCasaD 5 5 6).getD (134 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k134_5_6_50 k h.1 (by omega)
theorem s134_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 5 7 = true := by decide +kernel
theorem col134_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 6 v) = true := by decide +kernel
theorem col134_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 7 v) = true := by decide +kernel
theorem col134 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 134) 134 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col134_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col134_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s134_2_0
    · exact s134_2_1
    · exact s134_2_2
    · exact s134_2_3
    · exact s134_2_4
    · exact s134_2_5
    · exact s134_2_6
    · exact s134_2_7
  · fin_cases v
    · exact s134_3_0
    · exact s134_3_1
    · exact s134_3_2
    · exact s134_3_3
    · exact s134_3_4
    · exact s134_3_5
    · exact s134_3_6
    · exact s134_3_7
  · fin_cases v
    · exact s134_4_0
    · exact s134_4_1
    · exact s134_4_2
    · exact s134_4_3
    · exact s134_4_4
    · exact s134_4_5
    · exact s134_4_6
    · exact s134_4_7
  · fin_cases v
    · exact s134_5_0
    · exact s134_5_1
    · exact s134_5_2
    · exact s134_5_3
    · exact s134_5_4
    · exact s134_5_5
    · exact s134_5_6
    · exact s134_5_7
  · exact List.all_eq_true.mp col134_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col134_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
