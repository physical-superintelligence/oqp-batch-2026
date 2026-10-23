module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [165, 170). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col165_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 0 v) = true := by decide +kernel
theorem col165_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 1 v) = true := by decide +kernel
theorem col165_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 2 v) = true := by decide +kernel
theorem s165_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 0 = true := by decide +kernel
theorem s165_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 1 = true := by decide +kernel
theorem s165_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 2 = true := by decide +kernel
theorem k165_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k165_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k165_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s165_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k165_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k165_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k165_3_3_26 k h.1 (by omega)
theorem s165_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 4 = true := by decide +kernel
theorem s165_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 5 = true := by decide +kernel
theorem k165_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k165_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k165_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k165_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k165_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k165_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k165_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k165_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k165_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k165_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k165_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s165_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k165_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k165_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k165_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k165_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k165_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k165_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k165_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k165_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k165_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k165_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k165_3_6_130 k h.1 (by omega)
theorem s165_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 3 7 = true := by decide +kernel
theorem s165_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 0 = true := by decide +kernel
theorem s165_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 1 = true := by decide +kernel
theorem s165_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 2 = true := by decide +kernel
theorem s165_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 3 = true := by decide +kernel
theorem s165_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 4 = true := by decide +kernel
theorem s165_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 5 = true := by decide +kernel
theorem k165_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k165_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k165_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k165_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k165_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k165_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k165_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s165_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k165_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k165_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k165_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k165_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k165_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k165_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k165_4_6_126 k h.1 (by omega)
theorem s165_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 4 7 = true := by decide +kernel
theorem s165_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 0 = true := by decide +kernel
theorem s165_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 1 = true := by decide +kernel
theorem s165_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 2 = true := by decide +kernel
theorem s165_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 3 = true := by decide +kernel
theorem s165_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 4 = true := by decide +kernel
theorem s165_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 5 = true := by decide +kernel
theorem k165_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k165_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k165_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k165_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k165_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k165_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k165_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s165_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k165_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k165_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k165_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k165_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k165_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k165_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 165) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (165 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k165_5_6_126 k h.1 (by omega)
theorem s165_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 5 7 = true := by decide +kernel
theorem s165_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 0 = true := by decide +kernel
theorem s165_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 1 = true := by decide +kernel
theorem s165_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 2 = true := by decide +kernel
theorem s165_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 3 = true := by decide +kernel
theorem s165_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 4 = true := by decide +kernel
theorem s165_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 5 = true := by decide +kernel
theorem s165_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 6 = true := by decide +kernel
theorem k165_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k165_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k165_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k165_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k165_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s165_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k165_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k165_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k165_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k165_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 165) ((InDA1.TCasaD 6 6 7).getD (165 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k165_6_7_12 k h.1 (by omega)
theorem col165_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 7 v) = true := by decide +kernel
theorem col165 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 165) 165 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col165_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col165_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col165_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s165_3_0
    · exact s165_3_1
    · exact s165_3_2
    · exact s165_3_3
    · exact s165_3_4
    · exact s165_3_5
    · exact s165_3_6
    · exact s165_3_7
  · fin_cases v
    · exact s165_4_0
    · exact s165_4_1
    · exact s165_4_2
    · exact s165_4_3
    · exact s165_4_4
    · exact s165_4_5
    · exact s165_4_6
    · exact s165_4_7
  · fin_cases v
    · exact s165_5_0
    · exact s165_5_1
    · exact s165_5_2
    · exact s165_5_3
    · exact s165_5_4
    · exact s165_5_5
    · exact s165_5_6
    · exact s165_5_7
  · fin_cases v
    · exact s165_6_0
    · exact s165_6_1
    · exact s165_6_2
    · exact s165_6_3
    · exact s165_6_4
    · exact s165_6_5
    · exact s165_6_6
    · exact s165_6_7
  · exact List.all_eq_true.mp col165_7 v (List.mem_finRange v)
theorem col166_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 0 v) = true := by decide +kernel
theorem col166_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 1 v) = true := by decide +kernel
theorem col166_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 2 v) = true := by decide +kernel
theorem s166_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 0 = true := by decide +kernel
theorem s166_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 1 = true := by decide +kernel
theorem s166_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 2 = true := by decide +kernel
theorem k166_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k166_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k166_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s166_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k166_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k166_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k166_3_3_26 k h.1 (by omega)
theorem s166_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 4 = true := by decide +kernel
theorem s166_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 5 = true := by decide +kernel
theorem k166_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k166_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k166_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k166_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k166_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k166_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k166_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k166_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k166_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k166_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k166_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s166_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k166_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k166_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k166_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k166_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k166_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k166_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k166_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k166_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k166_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k166_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k166_3_6_130 k h.1 (by omega)
theorem s166_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 3 7 = true := by decide +kernel
theorem s166_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 0 = true := by decide +kernel
theorem s166_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 1 = true := by decide +kernel
theorem s166_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 2 = true := by decide +kernel
theorem s166_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 3 = true := by decide +kernel
theorem s166_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 4 = true := by decide +kernel
theorem s166_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 5 = true := by decide +kernel
theorem k166_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k166_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k166_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k166_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k166_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k166_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k166_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s166_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k166_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k166_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k166_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k166_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k166_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k166_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k166_4_6_126 k h.1 (by omega)
theorem s166_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 4 7 = true := by decide +kernel
theorem s166_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 0 = true := by decide +kernel
theorem s166_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 1 = true := by decide +kernel
theorem s166_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 2 = true := by decide +kernel
theorem s166_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 3 = true := by decide +kernel
theorem s166_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 4 = true := by decide +kernel
theorem s166_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 5 = true := by decide +kernel
theorem k166_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k166_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k166_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k166_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k166_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k166_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k166_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s166_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k166_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k166_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k166_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k166_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k166_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k166_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 166) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (166 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k166_5_6_126 k h.1 (by omega)
theorem s166_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 5 7 = true := by decide +kernel
theorem s166_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 0 = true := by decide +kernel
theorem s166_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 1 = true := by decide +kernel
theorem s166_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 2 = true := by decide +kernel
theorem s166_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 3 = true := by decide +kernel
theorem s166_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 4 = true := by decide +kernel
theorem s166_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 5 = true := by decide +kernel
theorem s166_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 6 = true := by decide +kernel
theorem k166_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k166_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k166_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k166_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k166_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s166_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k166_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k166_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k166_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k166_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 166) ((InDA1.TCasaD 6 6 7).getD (166 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k166_6_7_12 k h.1 (by omega)
theorem col166_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 7 v) = true := by decide +kernel
theorem col166 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 166) 166 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col166_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col166_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col166_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s166_3_0
    · exact s166_3_1
    · exact s166_3_2
    · exact s166_3_3
    · exact s166_3_4
    · exact s166_3_5
    · exact s166_3_6
    · exact s166_3_7
  · fin_cases v
    · exact s166_4_0
    · exact s166_4_1
    · exact s166_4_2
    · exact s166_4_3
    · exact s166_4_4
    · exact s166_4_5
    · exact s166_4_6
    · exact s166_4_7
  · fin_cases v
    · exact s166_5_0
    · exact s166_5_1
    · exact s166_5_2
    · exact s166_5_3
    · exact s166_5_4
    · exact s166_5_5
    · exact s166_5_6
    · exact s166_5_7
  · fin_cases v
    · exact s166_6_0
    · exact s166_6_1
    · exact s166_6_2
    · exact s166_6_3
    · exact s166_6_4
    · exact s166_6_5
    · exact s166_6_6
    · exact s166_6_7
  · exact List.all_eq_true.mp col166_7 v (List.mem_finRange v)
theorem col167_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 0 v) = true := by decide +kernel
theorem col167_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 1 v) = true := by decide +kernel
theorem col167_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 2 v) = true := by decide +kernel
theorem s167_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 0 = true := by decide +kernel
theorem s167_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 1 = true := by decide +kernel
theorem s167_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 2 = true := by decide +kernel
theorem k167_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k167_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k167_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s167_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k167_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k167_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k167_3_3_26 k h.1 (by omega)
theorem s167_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 4 = true := by decide +kernel
theorem s167_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 5 = true := by decide +kernel
theorem k167_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k167_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k167_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k167_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k167_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k167_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k167_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k167_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k167_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k167_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k167_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s167_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k167_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k167_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k167_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k167_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k167_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k167_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k167_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k167_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k167_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k167_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k167_3_6_130 k h.1 (by omega)
theorem s167_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 3 7 = true := by decide +kernel
theorem s167_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 0 = true := by decide +kernel
theorem s167_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 1 = true := by decide +kernel
theorem s167_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 2 = true := by decide +kernel
theorem s167_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 3 = true := by decide +kernel
theorem s167_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 4 = true := by decide +kernel
theorem s167_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 5 = true := by decide +kernel
theorem k167_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k167_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k167_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k167_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k167_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k167_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k167_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s167_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k167_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k167_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k167_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k167_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k167_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k167_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k167_4_6_126 k h.1 (by omega)
theorem s167_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 4 7 = true := by decide +kernel
theorem s167_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 0 = true := by decide +kernel
theorem s167_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 1 = true := by decide +kernel
theorem s167_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 2 = true := by decide +kernel
theorem s167_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 3 = true := by decide +kernel
theorem s167_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 4 = true := by decide +kernel
theorem s167_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 5 = true := by decide +kernel
theorem k167_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k167_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k167_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k167_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k167_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k167_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k167_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s167_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k167_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k167_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k167_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k167_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k167_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k167_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 167) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (167 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k167_5_6_126 k h.1 (by omega)
theorem s167_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 5 7 = true := by decide +kernel
theorem s167_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 0 = true := by decide +kernel
theorem s167_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 1 = true := by decide +kernel
theorem s167_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 2 = true := by decide +kernel
theorem s167_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 3 = true := by decide +kernel
theorem s167_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 4 = true := by decide +kernel
theorem s167_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 5 = true := by decide +kernel
theorem s167_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 6 = true := by decide +kernel
theorem k167_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k167_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k167_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k167_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k167_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s167_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k167_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k167_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k167_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k167_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 167) ((InDA1.TCasaD 6 6 7).getD (167 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k167_6_7_12 k h.1 (by omega)
theorem col167_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 7 v) = true := by decide +kernel
theorem col167 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 167) 167 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col167_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col167_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col167_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s167_3_0
    · exact s167_3_1
    · exact s167_3_2
    · exact s167_3_3
    · exact s167_3_4
    · exact s167_3_5
    · exact s167_3_6
    · exact s167_3_7
  · fin_cases v
    · exact s167_4_0
    · exact s167_4_1
    · exact s167_4_2
    · exact s167_4_3
    · exact s167_4_4
    · exact s167_4_5
    · exact s167_4_6
    · exact s167_4_7
  · fin_cases v
    · exact s167_5_0
    · exact s167_5_1
    · exact s167_5_2
    · exact s167_5_3
    · exact s167_5_4
    · exact s167_5_5
    · exact s167_5_6
    · exact s167_5_7
  · fin_cases v
    · exact s167_6_0
    · exact s167_6_1
    · exact s167_6_2
    · exact s167_6_3
    · exact s167_6_4
    · exact s167_6_5
    · exact s167_6_6
    · exact s167_6_7
  · exact List.all_eq_true.mp col167_7 v (List.mem_finRange v)
theorem col168_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 0 v) = true := by decide +kernel
theorem col168_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 1 v) = true := by decide +kernel
theorem col168_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 2 v) = true := by decide +kernel
theorem s168_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 0 = true := by decide +kernel
theorem s168_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 1 = true := by decide +kernel
theorem s168_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 2 = true := by decide +kernel
theorem k168_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k168_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k168_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s168_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k168_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k168_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k168_3_3_26 k h.1 (by omega)
theorem s168_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 4 = true := by decide +kernel
theorem s168_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 5 = true := by decide +kernel
theorem k168_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k168_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k168_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k168_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k168_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k168_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k168_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k168_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k168_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k168_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k168_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s168_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k168_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k168_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k168_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k168_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k168_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k168_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k168_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k168_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k168_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k168_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k168_3_6_130 k h.1 (by omega)
theorem s168_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 3 7 = true := by decide +kernel
theorem s168_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 0 = true := by decide +kernel
theorem s168_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 1 = true := by decide +kernel
theorem s168_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 2 = true := by decide +kernel
theorem s168_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 3 = true := by decide +kernel
theorem s168_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 4 = true := by decide +kernel
theorem s168_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 5 = true := by decide +kernel
theorem k168_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k168_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k168_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k168_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k168_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k168_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k168_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s168_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k168_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k168_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k168_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k168_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k168_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k168_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k168_4_6_126 k h.1 (by omega)
theorem s168_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 4 7 = true := by decide +kernel
theorem s168_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 0 = true := by decide +kernel
theorem s168_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 1 = true := by decide +kernel
theorem s168_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 2 = true := by decide +kernel
theorem s168_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 3 = true := by decide +kernel
theorem s168_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 4 = true := by decide +kernel
theorem s168_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 5 = true := by decide +kernel
theorem k168_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k168_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k168_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k168_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k168_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k168_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k168_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s168_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k168_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k168_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k168_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k168_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k168_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k168_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 168) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (168 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k168_5_6_126 k h.1 (by omega)
theorem s168_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 5 7 = true := by decide +kernel
theorem s168_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 0 = true := by decide +kernel
theorem s168_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 1 = true := by decide +kernel
theorem s168_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 2 = true := by decide +kernel
theorem s168_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 3 = true := by decide +kernel
theorem s168_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 4 = true := by decide +kernel
theorem s168_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 5 = true := by decide +kernel
theorem s168_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 6 = true := by decide +kernel
theorem k168_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k168_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k168_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k168_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k168_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s168_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k168_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k168_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k168_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k168_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 168) ((InDA1.TCasaD 6 6 7).getD (168 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k168_6_7_12 k h.1 (by omega)
theorem col168_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 7 v) = true := by decide +kernel
theorem col168 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 168) 168 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col168_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col168_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col168_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s168_3_0
    · exact s168_3_1
    · exact s168_3_2
    · exact s168_3_3
    · exact s168_3_4
    · exact s168_3_5
    · exact s168_3_6
    · exact s168_3_7
  · fin_cases v
    · exact s168_4_0
    · exact s168_4_1
    · exact s168_4_2
    · exact s168_4_3
    · exact s168_4_4
    · exact s168_4_5
    · exact s168_4_6
    · exact s168_4_7
  · fin_cases v
    · exact s168_5_0
    · exact s168_5_1
    · exact s168_5_2
    · exact s168_5_3
    · exact s168_5_4
    · exact s168_5_5
    · exact s168_5_6
    · exact s168_5_7
  · fin_cases v
    · exact s168_6_0
    · exact s168_6_1
    · exact s168_6_2
    · exact s168_6_3
    · exact s168_6_4
    · exact s168_6_5
    · exact s168_6_6
    · exact s168_6_7
  · exact List.all_eq_true.mp col168_7 v (List.mem_finRange v)
theorem col169_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 0 v) = true := by decide +kernel
theorem col169_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 1 v) = true := by decide +kernel
theorem col169_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 2 v) = true := by decide +kernel
theorem s169_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 0 = true := by decide +kernel
theorem s169_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 1 = true := by decide +kernel
theorem s169_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 2 = true := by decide +kernel
theorem k169_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k169_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k169_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s169_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k169_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k169_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k169_3_3_26 k h.1 (by omega)
theorem s169_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 4 = true := by decide +kernel
theorem s169_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 5 = true := by decide +kernel
theorem k169_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k169_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k169_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k169_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k169_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k169_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k169_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k169_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k169_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k169_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k169_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s169_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k169_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k169_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k169_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k169_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k169_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k169_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k169_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k169_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k169_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k169_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k169_3_6_130 k h.1 (by omega)
theorem s169_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 3 7 = true := by decide +kernel
theorem s169_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 0 = true := by decide +kernel
theorem s169_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 1 = true := by decide +kernel
theorem s169_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 2 = true := by decide +kernel
theorem s169_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 3 = true := by decide +kernel
theorem s169_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 4 = true := by decide +kernel
theorem s169_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 5 = true := by decide +kernel
theorem k169_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k169_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k169_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k169_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k169_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k169_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k169_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s169_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k169_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k169_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k169_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k169_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k169_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k169_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k169_4_6_126 k h.1 (by omega)
theorem s169_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 4 7 = true := by decide +kernel
theorem s169_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 0 = true := by decide +kernel
theorem s169_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 1 = true := by decide +kernel
theorem s169_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 2 = true := by decide +kernel
theorem s169_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 3 = true := by decide +kernel
theorem s169_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 4 = true := by decide +kernel
theorem s169_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 5 = true := by decide +kernel
theorem k169_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k169_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k169_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k169_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k169_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k169_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k169_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s169_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k169_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k169_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k169_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k169_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k169_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k169_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 169) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (169 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k169_5_6_126 k h.1 (by omega)
theorem s169_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 5 7 = true := by decide +kernel
theorem s169_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 0 = true := by decide +kernel
theorem s169_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 1 = true := by decide +kernel
theorem s169_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 2 = true := by decide +kernel
theorem s169_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 3 = true := by decide +kernel
theorem s169_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 4 = true := by decide +kernel
theorem s169_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 5 = true := by decide +kernel
theorem s169_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 6 = true := by decide +kernel
theorem k169_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k169_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k169_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k169_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k169_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s169_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k169_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k169_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k169_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k169_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 169) ((InDA1.TCasaD 6 6 7).getD (169 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k169_6_7_12 k h.1 (by omega)
theorem col169_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 7 v) = true := by decide +kernel
theorem col169 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 169) 169 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col169_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col169_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col169_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s169_3_0
    · exact s169_3_1
    · exact s169_3_2
    · exact s169_3_3
    · exact s169_3_4
    · exact s169_3_5
    · exact s169_3_6
    · exact s169_3_7
  · fin_cases v
    · exact s169_4_0
    · exact s169_4_1
    · exact s169_4_2
    · exact s169_4_3
    · exact s169_4_4
    · exact s169_4_5
    · exact s169_4_6
    · exact s169_4_7
  · fin_cases v
    · exact s169_5_0
    · exact s169_5_1
    · exact s169_5_2
    · exact s169_5_3
    · exact s169_5_4
    · exact s169_5_5
    · exact s169_5_6
    · exact s169_5_7
  · fin_cases v
    · exact s169_6_0
    · exact s169_6_1
    · exact s169_6_2
    · exact s169_6_3
    · exact s169_6_4
    · exact s169_6_5
    · exact s169_6_6
    · exact s169_6_7
  · exact List.all_eq_true.mp col169_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
