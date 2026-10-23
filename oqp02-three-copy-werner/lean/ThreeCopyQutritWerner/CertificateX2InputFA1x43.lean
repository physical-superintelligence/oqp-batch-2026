module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [215, 220). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col215_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 0 v) = true := by decide +kernel
theorem col215_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 1 v) = true := by decide +kernel
theorem col215_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 2 v) = true := by decide +kernel
theorem s215_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 0 = true := by decide +kernel
theorem s215_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 1 = true := by decide +kernel
theorem s215_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 2 = true := by decide +kernel
theorem k215_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k215_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k215_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s215_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k215_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k215_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k215_3_3_26 k h.1 (by omega)
theorem s215_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 4 = true := by decide +kernel
theorem s215_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 5 = true := by decide +kernel
theorem k215_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k215_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k215_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k215_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k215_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k215_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k215_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k215_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k215_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k215_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k215_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s215_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k215_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k215_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k215_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k215_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k215_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k215_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k215_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k215_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k215_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k215_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k215_3_6_130 k h.1 (by omega)
theorem s215_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 3 7 = true := by decide +kernel
theorem s215_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 0 = true := by decide +kernel
theorem s215_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 1 = true := by decide +kernel
theorem s215_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 2 = true := by decide +kernel
theorem s215_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 3 = true := by decide +kernel
theorem s215_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 4 = true := by decide +kernel
theorem s215_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 5 = true := by decide +kernel
theorem k215_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k215_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k215_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k215_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k215_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k215_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k215_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s215_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k215_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k215_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k215_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k215_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k215_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k215_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k215_4_6_126 k h.1 (by omega)
theorem s215_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 4 7 = true := by decide +kernel
theorem s215_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 0 = true := by decide +kernel
theorem s215_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 1 = true := by decide +kernel
theorem s215_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 2 = true := by decide +kernel
theorem s215_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 3 = true := by decide +kernel
theorem s215_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 4 = true := by decide +kernel
theorem s215_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 5 = true := by decide +kernel
theorem k215_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k215_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k215_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k215_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k215_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k215_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k215_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s215_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k215_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k215_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k215_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k215_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k215_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k215_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 215) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (215 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k215_5_6_126 k h.1 (by omega)
theorem s215_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 5 7 = true := by decide +kernel
theorem s215_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 0 = true := by decide +kernel
theorem s215_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 1 = true := by decide +kernel
theorem s215_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 2 = true := by decide +kernel
theorem s215_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 3 = true := by decide +kernel
theorem s215_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 4 = true := by decide +kernel
theorem s215_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 5 = true := by decide +kernel
theorem s215_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 6 = true := by decide +kernel
theorem k215_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k215_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k215_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k215_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k215_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s215_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k215_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k215_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k215_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k215_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 215) ((InDA1.TCasaD 6 6 7).getD (215 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k215_6_7_12 k h.1 (by omega)
theorem col215_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 7 v) = true := by decide +kernel
theorem col215 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 215) 215 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col215_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col215_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col215_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s215_3_0
    · exact s215_3_1
    · exact s215_3_2
    · exact s215_3_3
    · exact s215_3_4
    · exact s215_3_5
    · exact s215_3_6
    · exact s215_3_7
  · fin_cases v
    · exact s215_4_0
    · exact s215_4_1
    · exact s215_4_2
    · exact s215_4_3
    · exact s215_4_4
    · exact s215_4_5
    · exact s215_4_6
    · exact s215_4_7
  · fin_cases v
    · exact s215_5_0
    · exact s215_5_1
    · exact s215_5_2
    · exact s215_5_3
    · exact s215_5_4
    · exact s215_5_5
    · exact s215_5_6
    · exact s215_5_7
  · fin_cases v
    · exact s215_6_0
    · exact s215_6_1
    · exact s215_6_2
    · exact s215_6_3
    · exact s215_6_4
    · exact s215_6_5
    · exact s215_6_6
    · exact s215_6_7
  · exact List.all_eq_true.mp col215_7 v (List.mem_finRange v)
theorem col216_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 0 v) = true := by decide +kernel
theorem col216_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 1 v) = true := by decide +kernel
theorem col216_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 2 v) = true := by decide +kernel
theorem s216_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 0 = true := by decide +kernel
theorem s216_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 1 = true := by decide +kernel
theorem s216_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 2 = true := by decide +kernel
theorem k216_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k216_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k216_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s216_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k216_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k216_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k216_3_3_26 k h.1 (by omega)
theorem s216_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 4 = true := by decide +kernel
theorem s216_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 5 = true := by decide +kernel
theorem k216_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k216_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k216_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k216_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k216_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k216_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k216_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k216_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k216_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k216_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k216_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s216_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k216_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k216_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k216_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k216_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k216_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k216_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k216_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k216_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k216_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k216_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k216_3_6_130 k h.1 (by omega)
theorem s216_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 3 7 = true := by decide +kernel
theorem s216_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 0 = true := by decide +kernel
theorem s216_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 1 = true := by decide +kernel
theorem s216_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 2 = true := by decide +kernel
theorem s216_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 3 = true := by decide +kernel
theorem s216_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 4 = true := by decide +kernel
theorem s216_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 5 = true := by decide +kernel
theorem k216_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k216_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k216_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k216_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k216_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k216_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k216_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s216_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k216_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k216_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k216_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k216_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k216_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k216_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k216_4_6_126 k h.1 (by omega)
theorem s216_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 4 7 = true := by decide +kernel
theorem s216_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 0 = true := by decide +kernel
theorem s216_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 1 = true := by decide +kernel
theorem s216_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 2 = true := by decide +kernel
theorem s216_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 3 = true := by decide +kernel
theorem s216_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 4 = true := by decide +kernel
theorem s216_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 5 = true := by decide +kernel
theorem k216_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k216_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k216_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k216_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k216_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k216_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k216_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s216_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k216_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k216_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k216_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k216_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k216_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k216_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k216_5_6_126 k h.1 (by omega)
theorem s216_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 5 7 = true := by decide +kernel
theorem s216_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 0 = true := by decide +kernel
theorem s216_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 1 = true := by decide +kernel
theorem s216_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 2 = true := by decide +kernel
theorem k216_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k216_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k216_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k216_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k216_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k216_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k216_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k216_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k216_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k216_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k216_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k216_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s216_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k216_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k216_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k216_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k216_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k216_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k216_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k216_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k216_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k216_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k216_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k216_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k216_6_3_33 k h.1 (by omega)
theorem k216_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k216_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k216_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k216_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k216_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k216_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k216_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s216_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k216_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k216_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k216_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k216_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k216_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k216_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k216_6_4_18 k h.1 (by omega)
theorem k216_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k216_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k216_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k216_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k216_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k216_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k216_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s216_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k216_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k216_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k216_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k216_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k216_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k216_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k216_6_5_18 k h.1 (by omega)
theorem k216_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k216_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k216_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k216_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k216_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k216_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k216_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k216_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k216_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k216_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k216_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k216_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k216_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k216_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k216_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k216_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k216_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k216_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k216_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k216_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k216_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k216_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k216_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k216_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k216_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k216_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k216_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k216_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k216_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k216_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k216_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k216_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k216_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k216_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k216_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k216_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k216_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k216_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k216_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k216_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k216_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k216_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k216_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k216_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k216_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k216_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s216_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k216_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k216_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k216_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k216_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k216_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k216_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k216_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k216_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k216_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k216_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k216_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k216_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k216_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k216_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k216_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k216_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k216_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k216_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k216_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k216_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k216_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k216_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k216_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k216_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k216_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k216_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k216_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k216_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k216_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k216_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k216_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k216_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k216_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k216_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k216_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k216_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k216_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k216_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k216_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k216_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k216_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k216_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k216_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k216_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k216_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k216_6_6_135 k h.1 (by omega)
theorem k216_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k216_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k216_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k216_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k216_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s216_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k216_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k216_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k216_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k216_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 216) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (216 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k216_6_7_12 k h.1 (by omega)
theorem col216_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 7 v) = true := by decide +kernel
theorem col216 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 216) 216 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col216_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col216_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col216_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s216_3_0
    · exact s216_3_1
    · exact s216_3_2
    · exact s216_3_3
    · exact s216_3_4
    · exact s216_3_5
    · exact s216_3_6
    · exact s216_3_7
  · fin_cases v
    · exact s216_4_0
    · exact s216_4_1
    · exact s216_4_2
    · exact s216_4_3
    · exact s216_4_4
    · exact s216_4_5
    · exact s216_4_6
    · exact s216_4_7
  · fin_cases v
    · exact s216_5_0
    · exact s216_5_1
    · exact s216_5_2
    · exact s216_5_3
    · exact s216_5_4
    · exact s216_5_5
    · exact s216_5_6
    · exact s216_5_7
  · fin_cases v
    · exact s216_6_0
    · exact s216_6_1
    · exact s216_6_2
    · exact s216_6_3
    · exact s216_6_4
    · exact s216_6_5
    · exact s216_6_6
    · exact s216_6_7
  · exact List.all_eq_true.mp col216_7 v (List.mem_finRange v)
theorem col217_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 0 v) = true := by decide +kernel
theorem col217_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 1 v) = true := by decide +kernel
theorem col217_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 2 v) = true := by decide +kernel
theorem s217_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 0 = true := by decide +kernel
theorem s217_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 1 = true := by decide +kernel
theorem s217_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 2 = true := by decide +kernel
theorem k217_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k217_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k217_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s217_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k217_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k217_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k217_3_3_26 k h.1 (by omega)
theorem s217_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 4 = true := by decide +kernel
theorem s217_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 5 = true := by decide +kernel
theorem k217_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k217_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k217_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k217_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k217_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k217_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k217_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k217_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k217_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k217_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k217_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s217_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k217_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k217_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k217_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k217_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k217_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k217_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k217_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k217_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k217_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k217_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k217_3_6_130 k h.1 (by omega)
theorem s217_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 3 7 = true := by decide +kernel
theorem s217_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 0 = true := by decide +kernel
theorem s217_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 1 = true := by decide +kernel
theorem s217_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 2 = true := by decide +kernel
theorem s217_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 3 = true := by decide +kernel
theorem s217_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 4 = true := by decide +kernel
theorem s217_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 5 = true := by decide +kernel
theorem k217_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k217_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k217_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k217_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k217_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k217_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k217_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s217_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k217_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k217_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k217_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k217_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k217_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k217_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k217_4_6_126 k h.1 (by omega)
theorem s217_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 4 7 = true := by decide +kernel
theorem s217_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 0 = true := by decide +kernel
theorem s217_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 1 = true := by decide +kernel
theorem s217_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 2 = true := by decide +kernel
theorem s217_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 3 = true := by decide +kernel
theorem s217_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 4 = true := by decide +kernel
theorem s217_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 5 = true := by decide +kernel
theorem k217_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k217_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k217_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k217_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k217_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k217_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k217_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s217_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k217_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k217_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k217_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k217_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k217_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k217_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k217_5_6_126 k h.1 (by omega)
theorem s217_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 5 7 = true := by decide +kernel
theorem s217_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 0 = true := by decide +kernel
theorem s217_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 1 = true := by decide +kernel
theorem s217_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 2 = true := by decide +kernel
theorem k217_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k217_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k217_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k217_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k217_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k217_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k217_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k217_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k217_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k217_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k217_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k217_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s217_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k217_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k217_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k217_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k217_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k217_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k217_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k217_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k217_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k217_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k217_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k217_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k217_6_3_33 k h.1 (by omega)
theorem k217_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k217_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k217_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k217_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k217_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k217_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k217_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s217_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k217_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k217_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k217_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k217_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k217_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k217_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k217_6_4_18 k h.1 (by omega)
theorem k217_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k217_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k217_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k217_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k217_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k217_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k217_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s217_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k217_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k217_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k217_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k217_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k217_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k217_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k217_6_5_18 k h.1 (by omega)
theorem k217_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k217_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k217_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k217_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k217_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k217_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k217_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k217_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k217_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k217_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k217_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k217_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k217_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k217_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k217_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k217_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k217_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k217_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k217_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k217_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k217_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k217_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k217_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k217_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k217_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k217_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k217_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k217_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k217_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k217_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k217_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k217_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k217_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k217_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k217_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k217_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k217_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k217_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k217_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k217_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k217_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k217_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k217_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k217_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k217_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k217_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s217_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k217_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k217_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k217_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k217_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k217_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k217_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k217_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k217_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k217_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k217_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k217_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k217_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k217_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k217_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k217_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k217_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k217_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k217_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k217_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k217_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k217_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k217_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k217_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k217_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k217_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k217_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k217_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k217_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k217_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k217_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k217_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k217_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k217_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k217_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k217_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k217_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k217_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k217_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k217_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k217_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k217_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k217_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k217_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k217_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k217_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k217_6_6_135 k h.1 (by omega)
theorem k217_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k217_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k217_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k217_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k217_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s217_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k217_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k217_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k217_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k217_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 217) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (217 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k217_6_7_12 k h.1 (by omega)
theorem col217_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 7 v) = true := by decide +kernel
theorem col217 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 217) 217 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col217_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col217_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col217_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s217_3_0
    · exact s217_3_1
    · exact s217_3_2
    · exact s217_3_3
    · exact s217_3_4
    · exact s217_3_5
    · exact s217_3_6
    · exact s217_3_7
  · fin_cases v
    · exact s217_4_0
    · exact s217_4_1
    · exact s217_4_2
    · exact s217_4_3
    · exact s217_4_4
    · exact s217_4_5
    · exact s217_4_6
    · exact s217_4_7
  · fin_cases v
    · exact s217_5_0
    · exact s217_5_1
    · exact s217_5_2
    · exact s217_5_3
    · exact s217_5_4
    · exact s217_5_5
    · exact s217_5_6
    · exact s217_5_7
  · fin_cases v
    · exact s217_6_0
    · exact s217_6_1
    · exact s217_6_2
    · exact s217_6_3
    · exact s217_6_4
    · exact s217_6_5
    · exact s217_6_6
    · exact s217_6_7
  · exact List.all_eq_true.mp col217_7 v (List.mem_finRange v)
theorem col218_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 0 v) = true := by decide +kernel
theorem col218_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 1 v) = true := by decide +kernel
theorem col218_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 2 v) = true := by decide +kernel
theorem s218_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 0 = true := by decide +kernel
theorem s218_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 1 = true := by decide +kernel
theorem s218_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 2 = true := by decide +kernel
theorem k218_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k218_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k218_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s218_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k218_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k218_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k218_3_3_26 k h.1 (by omega)
theorem s218_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 4 = true := by decide +kernel
theorem s218_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 5 = true := by decide +kernel
theorem k218_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k218_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k218_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k218_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k218_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k218_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k218_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k218_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k218_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k218_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k218_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s218_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k218_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k218_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k218_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k218_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k218_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k218_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k218_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k218_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k218_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k218_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k218_3_6_130 k h.1 (by omega)
theorem s218_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 3 7 = true := by decide +kernel
theorem s218_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 0 = true := by decide +kernel
theorem s218_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 1 = true := by decide +kernel
theorem s218_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 2 = true := by decide +kernel
theorem s218_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 3 = true := by decide +kernel
theorem s218_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 4 = true := by decide +kernel
theorem s218_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 5 = true := by decide +kernel
theorem k218_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k218_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k218_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k218_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k218_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k218_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k218_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s218_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k218_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k218_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k218_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k218_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k218_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k218_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k218_4_6_126 k h.1 (by omega)
theorem s218_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 4 7 = true := by decide +kernel
theorem s218_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 0 = true := by decide +kernel
theorem s218_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 1 = true := by decide +kernel
theorem s218_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 2 = true := by decide +kernel
theorem s218_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 3 = true := by decide +kernel
theorem s218_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 4 = true := by decide +kernel
theorem s218_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 5 = true := by decide +kernel
theorem k218_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k218_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k218_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k218_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k218_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k218_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k218_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s218_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k218_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k218_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k218_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k218_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k218_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k218_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k218_5_6_126 k h.1 (by omega)
theorem s218_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 5 7 = true := by decide +kernel
theorem s218_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 0 = true := by decide +kernel
theorem s218_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 1 = true := by decide +kernel
theorem s218_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 2 = true := by decide +kernel
theorem k218_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k218_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k218_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k218_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k218_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k218_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k218_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k218_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k218_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k218_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k218_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k218_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s218_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k218_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k218_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k218_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k218_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k218_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k218_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k218_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k218_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k218_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k218_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k218_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k218_6_3_33 k h.1 (by omega)
theorem k218_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k218_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k218_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k218_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k218_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k218_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k218_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s218_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k218_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k218_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k218_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k218_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k218_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k218_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k218_6_4_18 k h.1 (by omega)
theorem k218_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k218_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k218_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k218_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k218_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k218_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k218_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s218_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k218_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k218_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k218_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k218_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k218_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k218_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k218_6_5_18 k h.1 (by omega)
theorem k218_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k218_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k218_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k218_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k218_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k218_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k218_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k218_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k218_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k218_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k218_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k218_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k218_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k218_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k218_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k218_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k218_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k218_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k218_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k218_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k218_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k218_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k218_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k218_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k218_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k218_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k218_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k218_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k218_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k218_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k218_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k218_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k218_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k218_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k218_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k218_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k218_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k218_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k218_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k218_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k218_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k218_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k218_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k218_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k218_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k218_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s218_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k218_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k218_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k218_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k218_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k218_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k218_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k218_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k218_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k218_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k218_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k218_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k218_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k218_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k218_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k218_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k218_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k218_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k218_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k218_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k218_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k218_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k218_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k218_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k218_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k218_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k218_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k218_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k218_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k218_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k218_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k218_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k218_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k218_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k218_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k218_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k218_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k218_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k218_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k218_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k218_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k218_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k218_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k218_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k218_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k218_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k218_6_6_135 k h.1 (by omega)
theorem k218_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k218_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k218_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k218_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k218_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s218_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k218_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k218_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k218_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k218_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 218) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (218 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k218_6_7_12 k h.1 (by omega)
theorem col218_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 7 v) = true := by decide +kernel
theorem col218 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 218) 218 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col218_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col218_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col218_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s218_3_0
    · exact s218_3_1
    · exact s218_3_2
    · exact s218_3_3
    · exact s218_3_4
    · exact s218_3_5
    · exact s218_3_6
    · exact s218_3_7
  · fin_cases v
    · exact s218_4_0
    · exact s218_4_1
    · exact s218_4_2
    · exact s218_4_3
    · exact s218_4_4
    · exact s218_4_5
    · exact s218_4_6
    · exact s218_4_7
  · fin_cases v
    · exact s218_5_0
    · exact s218_5_1
    · exact s218_5_2
    · exact s218_5_3
    · exact s218_5_4
    · exact s218_5_5
    · exact s218_5_6
    · exact s218_5_7
  · fin_cases v
    · exact s218_6_0
    · exact s218_6_1
    · exact s218_6_2
    · exact s218_6_3
    · exact s218_6_4
    · exact s218_6_5
    · exact s218_6_6
    · exact s218_6_7
  · exact List.all_eq_true.mp col218_7 v (List.mem_finRange v)
theorem col219_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 0 v) = true := by decide +kernel
theorem col219_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 1 v) = true := by decide +kernel
theorem col219_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 2 v) = true := by decide +kernel
theorem s219_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 0 = true := by decide +kernel
theorem s219_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 1 = true := by decide +kernel
theorem s219_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 2 = true := by decide +kernel
theorem k219_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k219_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k219_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s219_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k219_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k219_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k219_3_3_26 k h.1 (by omega)
theorem s219_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 4 = true := by decide +kernel
theorem s219_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 5 = true := by decide +kernel
theorem k219_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k219_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k219_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k219_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k219_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k219_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k219_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k219_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k219_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k219_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k219_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s219_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k219_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k219_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k219_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k219_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k219_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k219_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k219_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k219_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k219_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k219_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k219_3_6_130 k h.1 (by omega)
theorem s219_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 3 7 = true := by decide +kernel
theorem s219_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 0 = true := by decide +kernel
theorem s219_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 1 = true := by decide +kernel
theorem s219_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 2 = true := by decide +kernel
theorem s219_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 3 = true := by decide +kernel
theorem s219_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 4 = true := by decide +kernel
theorem s219_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 5 = true := by decide +kernel
theorem k219_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k219_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k219_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k219_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k219_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k219_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k219_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s219_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k219_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k219_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k219_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k219_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k219_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k219_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k219_4_6_126 k h.1 (by omega)
theorem s219_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 4 7 = true := by decide +kernel
theorem s219_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 0 = true := by decide +kernel
theorem s219_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 1 = true := by decide +kernel
theorem s219_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 2 = true := by decide +kernel
theorem s219_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 3 = true := by decide +kernel
theorem s219_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 4 = true := by decide +kernel
theorem s219_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 5 = true := by decide +kernel
theorem k219_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k219_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k219_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k219_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k219_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k219_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k219_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s219_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k219_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k219_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k219_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k219_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k219_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k219_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k219_5_6_126 k h.1 (by omega)
theorem s219_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 5 7 = true := by decide +kernel
theorem s219_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 0 = true := by decide +kernel
theorem s219_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 1 = true := by decide +kernel
theorem s219_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 2 = true := by decide +kernel
theorem k219_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k219_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k219_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k219_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k219_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k219_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k219_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k219_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k219_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k219_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k219_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k219_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s219_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k219_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k219_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k219_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k219_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k219_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k219_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k219_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k219_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k219_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k219_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k219_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k219_6_3_33 k h.1 (by omega)
theorem k219_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k219_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k219_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k219_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k219_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k219_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k219_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s219_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k219_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k219_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k219_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k219_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k219_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k219_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k219_6_4_18 k h.1 (by omega)
theorem k219_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k219_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k219_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k219_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k219_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k219_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k219_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s219_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k219_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k219_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k219_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k219_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k219_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k219_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k219_6_5_18 k h.1 (by omega)
theorem k219_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k219_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k219_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k219_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k219_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k219_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k219_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k219_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k219_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k219_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k219_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k219_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k219_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k219_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k219_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k219_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k219_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k219_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k219_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k219_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k219_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k219_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k219_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k219_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k219_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k219_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k219_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k219_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k219_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k219_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k219_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k219_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k219_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k219_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k219_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k219_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k219_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k219_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k219_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k219_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k219_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k219_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k219_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k219_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k219_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k219_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s219_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k219_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k219_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k219_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k219_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k219_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k219_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k219_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k219_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k219_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k219_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k219_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k219_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k219_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k219_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k219_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k219_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k219_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k219_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k219_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k219_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k219_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k219_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k219_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k219_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k219_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k219_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k219_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k219_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k219_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k219_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k219_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k219_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k219_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k219_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k219_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k219_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k219_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k219_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k219_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k219_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k219_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k219_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k219_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k219_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k219_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k219_6_6_135 k h.1 (by omega)
theorem k219_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k219_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k219_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k219_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k219_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s219_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k219_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k219_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k219_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k219_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 219) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (219 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k219_6_7_12 k h.1 (by omega)
theorem col219_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 7 v) = true := by decide +kernel
theorem col219 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 219) 219 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col219_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col219_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col219_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s219_3_0
    · exact s219_3_1
    · exact s219_3_2
    · exact s219_3_3
    · exact s219_3_4
    · exact s219_3_5
    · exact s219_3_6
    · exact s219_3_7
  · fin_cases v
    · exact s219_4_0
    · exact s219_4_1
    · exact s219_4_2
    · exact s219_4_3
    · exact s219_4_4
    · exact s219_4_5
    · exact s219_4_6
    · exact s219_4_7
  · fin_cases v
    · exact s219_5_0
    · exact s219_5_1
    · exact s219_5_2
    · exact s219_5_3
    · exact s219_5_4
    · exact s219_5_5
    · exact s219_5_6
    · exact s219_5_7
  · fin_cases v
    · exact s219_6_0
    · exact s219_6_1
    · exact s219_6_2
    · exact s219_6_3
    · exact s219_6_4
    · exact s219_6_5
    · exact s219_6_6
    · exact s219_6_7
  · exact List.all_eq_true.mp col219_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
