module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [155, 160). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col155_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 0 v) = true := by decide +kernel
theorem col155_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 1 v) = true := by decide +kernel
theorem col155_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 2 v) = true := by decide +kernel
theorem s155_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 0 = true := by decide +kernel
theorem s155_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 1 = true := by decide +kernel
theorem s155_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 2 = true := by decide +kernel
theorem k155_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k155_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k155_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s155_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k155_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k155_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k155_3_3_26 k h.1 (by omega)
theorem s155_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 4 = true := by decide +kernel
theorem s155_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 5 = true := by decide +kernel
theorem k155_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k155_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k155_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k155_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k155_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k155_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k155_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k155_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k155_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k155_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k155_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s155_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k155_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k155_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k155_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k155_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k155_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k155_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k155_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k155_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k155_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k155_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k155_3_6_130 k h.1 (by omega)
theorem s155_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 3 7 = true := by decide +kernel
theorem s155_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 0 = true := by decide +kernel
theorem s155_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 1 = true := by decide +kernel
theorem s155_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 2 = true := by decide +kernel
theorem s155_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 3 = true := by decide +kernel
theorem s155_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 4 = true := by decide +kernel
theorem s155_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 5 = true := by decide +kernel
theorem k155_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k155_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k155_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k155_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k155_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k155_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k155_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s155_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k155_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k155_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k155_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k155_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k155_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k155_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k155_4_6_126 k h.1 (by omega)
theorem s155_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 4 7 = true := by decide +kernel
theorem s155_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 0 = true := by decide +kernel
theorem s155_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 1 = true := by decide +kernel
theorem s155_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 2 = true := by decide +kernel
theorem s155_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 3 = true := by decide +kernel
theorem s155_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 4 = true := by decide +kernel
theorem s155_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 5 = true := by decide +kernel
theorem k155_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k155_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k155_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k155_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k155_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k155_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k155_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s155_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k155_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k155_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k155_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k155_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k155_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k155_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 155) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (155 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k155_5_6_126 k h.1 (by omega)
theorem s155_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 5 7 = true := by decide +kernel
theorem s155_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 0 = true := by decide +kernel
theorem s155_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 1 = true := by decide +kernel
theorem s155_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 2 = true := by decide +kernel
theorem s155_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 3 = true := by decide +kernel
theorem s155_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 4 = true := by decide +kernel
theorem s155_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 5 = true := by decide +kernel
theorem s155_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 6 = true := by decide +kernel
theorem k155_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k155_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k155_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k155_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k155_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s155_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k155_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k155_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k155_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k155_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 155) ((InDA1.TCasaD 6 6 7).getD (155 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k155_6_7_12 k h.1 (by omega)
theorem col155_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 7 v) = true := by decide +kernel
theorem col155 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 155) 155 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col155_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col155_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col155_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s155_3_0
    · exact s155_3_1
    · exact s155_3_2
    · exact s155_3_3
    · exact s155_3_4
    · exact s155_3_5
    · exact s155_3_6
    · exact s155_3_7
  · fin_cases v
    · exact s155_4_0
    · exact s155_4_1
    · exact s155_4_2
    · exact s155_4_3
    · exact s155_4_4
    · exact s155_4_5
    · exact s155_4_6
    · exact s155_4_7
  · fin_cases v
    · exact s155_5_0
    · exact s155_5_1
    · exact s155_5_2
    · exact s155_5_3
    · exact s155_5_4
    · exact s155_5_5
    · exact s155_5_6
    · exact s155_5_7
  · fin_cases v
    · exact s155_6_0
    · exact s155_6_1
    · exact s155_6_2
    · exact s155_6_3
    · exact s155_6_4
    · exact s155_6_5
    · exact s155_6_6
    · exact s155_6_7
  · exact List.all_eq_true.mp col155_7 v (List.mem_finRange v)
theorem col156_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 0 v) = true := by decide +kernel
theorem col156_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 1 v) = true := by decide +kernel
theorem col156_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 2 v) = true := by decide +kernel
theorem s156_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 0 = true := by decide +kernel
theorem s156_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 1 = true := by decide +kernel
theorem s156_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 2 = true := by decide +kernel
theorem k156_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k156_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k156_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s156_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k156_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k156_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k156_3_3_26 k h.1 (by omega)
theorem s156_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 4 = true := by decide +kernel
theorem s156_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 5 = true := by decide +kernel
theorem k156_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k156_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k156_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k156_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k156_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k156_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k156_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k156_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k156_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k156_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k156_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s156_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k156_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k156_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k156_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k156_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k156_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k156_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k156_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k156_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k156_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k156_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k156_3_6_130 k h.1 (by omega)
theorem s156_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 3 7 = true := by decide +kernel
theorem s156_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 0 = true := by decide +kernel
theorem s156_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 1 = true := by decide +kernel
theorem s156_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 2 = true := by decide +kernel
theorem s156_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 3 = true := by decide +kernel
theorem s156_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 4 = true := by decide +kernel
theorem s156_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 5 = true := by decide +kernel
theorem k156_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k156_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k156_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k156_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k156_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k156_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k156_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s156_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k156_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k156_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k156_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k156_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k156_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k156_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k156_4_6_126 k h.1 (by omega)
theorem s156_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 4 7 = true := by decide +kernel
theorem s156_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 0 = true := by decide +kernel
theorem s156_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 1 = true := by decide +kernel
theorem s156_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 2 = true := by decide +kernel
theorem s156_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 3 = true := by decide +kernel
theorem s156_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 4 = true := by decide +kernel
theorem s156_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 5 = true := by decide +kernel
theorem k156_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k156_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k156_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k156_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k156_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k156_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k156_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s156_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k156_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k156_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k156_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k156_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k156_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k156_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 156) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (156 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k156_5_6_126 k h.1 (by omega)
theorem s156_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 5 7 = true := by decide +kernel
theorem s156_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 0 = true := by decide +kernel
theorem s156_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 1 = true := by decide +kernel
theorem s156_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 2 = true := by decide +kernel
theorem s156_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 3 = true := by decide +kernel
theorem s156_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 4 = true := by decide +kernel
theorem s156_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 5 = true := by decide +kernel
theorem s156_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 6 = true := by decide +kernel
theorem k156_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k156_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k156_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k156_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k156_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s156_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k156_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k156_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k156_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k156_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 156) ((InDA1.TCasaD 6 6 7).getD (156 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k156_6_7_12 k h.1 (by omega)
theorem col156_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 7 v) = true := by decide +kernel
theorem col156 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 156) 156 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col156_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col156_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col156_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s156_3_0
    · exact s156_3_1
    · exact s156_3_2
    · exact s156_3_3
    · exact s156_3_4
    · exact s156_3_5
    · exact s156_3_6
    · exact s156_3_7
  · fin_cases v
    · exact s156_4_0
    · exact s156_4_1
    · exact s156_4_2
    · exact s156_4_3
    · exact s156_4_4
    · exact s156_4_5
    · exact s156_4_6
    · exact s156_4_7
  · fin_cases v
    · exact s156_5_0
    · exact s156_5_1
    · exact s156_5_2
    · exact s156_5_3
    · exact s156_5_4
    · exact s156_5_5
    · exact s156_5_6
    · exact s156_5_7
  · fin_cases v
    · exact s156_6_0
    · exact s156_6_1
    · exact s156_6_2
    · exact s156_6_3
    · exact s156_6_4
    · exact s156_6_5
    · exact s156_6_6
    · exact s156_6_7
  · exact List.all_eq_true.mp col156_7 v (List.mem_finRange v)
theorem col157_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 0 v) = true := by decide +kernel
theorem col157_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 1 v) = true := by decide +kernel
theorem col157_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 2 v) = true := by decide +kernel
theorem s157_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 0 = true := by decide +kernel
theorem s157_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 1 = true := by decide +kernel
theorem s157_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 2 = true := by decide +kernel
theorem k157_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k157_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k157_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s157_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k157_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k157_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k157_3_3_26 k h.1 (by omega)
theorem s157_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 4 = true := by decide +kernel
theorem s157_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 5 = true := by decide +kernel
theorem k157_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k157_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k157_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k157_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k157_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k157_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k157_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k157_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k157_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k157_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k157_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s157_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k157_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k157_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k157_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k157_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k157_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k157_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k157_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k157_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k157_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k157_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k157_3_6_130 k h.1 (by omega)
theorem s157_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 3 7 = true := by decide +kernel
theorem s157_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 0 = true := by decide +kernel
theorem s157_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 1 = true := by decide +kernel
theorem s157_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 2 = true := by decide +kernel
theorem s157_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 3 = true := by decide +kernel
theorem s157_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 4 = true := by decide +kernel
theorem s157_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 5 = true := by decide +kernel
theorem k157_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k157_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k157_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k157_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k157_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k157_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k157_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s157_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k157_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k157_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k157_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k157_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k157_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k157_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k157_4_6_126 k h.1 (by omega)
theorem s157_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 4 7 = true := by decide +kernel
theorem s157_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 0 = true := by decide +kernel
theorem s157_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 1 = true := by decide +kernel
theorem s157_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 2 = true := by decide +kernel
theorem s157_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 3 = true := by decide +kernel
theorem s157_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 4 = true := by decide +kernel
theorem s157_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 5 = true := by decide +kernel
theorem k157_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k157_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k157_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k157_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k157_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k157_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k157_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s157_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k157_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k157_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k157_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k157_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k157_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k157_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 157) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (157 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k157_5_6_126 k h.1 (by omega)
theorem s157_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 5 7 = true := by decide +kernel
theorem s157_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 0 = true := by decide +kernel
theorem s157_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 1 = true := by decide +kernel
theorem s157_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 2 = true := by decide +kernel
theorem s157_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 3 = true := by decide +kernel
theorem s157_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 4 = true := by decide +kernel
theorem s157_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 5 = true := by decide +kernel
theorem s157_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 6 = true := by decide +kernel
theorem k157_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k157_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k157_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k157_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k157_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s157_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k157_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k157_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k157_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k157_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 157) ((InDA1.TCasaD 6 6 7).getD (157 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k157_6_7_12 k h.1 (by omega)
theorem col157_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 7 v) = true := by decide +kernel
theorem col157 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 157) 157 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col157_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col157_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col157_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s157_3_0
    · exact s157_3_1
    · exact s157_3_2
    · exact s157_3_3
    · exact s157_3_4
    · exact s157_3_5
    · exact s157_3_6
    · exact s157_3_7
  · fin_cases v
    · exact s157_4_0
    · exact s157_4_1
    · exact s157_4_2
    · exact s157_4_3
    · exact s157_4_4
    · exact s157_4_5
    · exact s157_4_6
    · exact s157_4_7
  · fin_cases v
    · exact s157_5_0
    · exact s157_5_1
    · exact s157_5_2
    · exact s157_5_3
    · exact s157_5_4
    · exact s157_5_5
    · exact s157_5_6
    · exact s157_5_7
  · fin_cases v
    · exact s157_6_0
    · exact s157_6_1
    · exact s157_6_2
    · exact s157_6_3
    · exact s157_6_4
    · exact s157_6_5
    · exact s157_6_6
    · exact s157_6_7
  · exact List.all_eq_true.mp col157_7 v (List.mem_finRange v)
theorem col158_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 0 v) = true := by decide +kernel
theorem col158_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 1 v) = true := by decide +kernel
theorem col158_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 2 v) = true := by decide +kernel
theorem s158_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 0 = true := by decide +kernel
theorem s158_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 1 = true := by decide +kernel
theorem s158_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 2 = true := by decide +kernel
theorem k158_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k158_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k158_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s158_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k158_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k158_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k158_3_3_26 k h.1 (by omega)
theorem s158_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 4 = true := by decide +kernel
theorem s158_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 5 = true := by decide +kernel
theorem k158_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k158_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k158_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k158_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k158_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k158_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k158_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k158_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k158_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k158_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k158_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s158_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k158_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k158_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k158_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k158_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k158_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k158_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k158_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k158_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k158_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k158_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k158_3_6_130 k h.1 (by omega)
theorem s158_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 3 7 = true := by decide +kernel
theorem s158_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 0 = true := by decide +kernel
theorem s158_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 1 = true := by decide +kernel
theorem s158_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 2 = true := by decide +kernel
theorem s158_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 3 = true := by decide +kernel
theorem s158_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 4 = true := by decide +kernel
theorem s158_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 5 = true := by decide +kernel
theorem k158_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k158_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k158_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k158_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k158_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k158_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k158_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s158_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k158_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k158_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k158_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k158_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k158_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k158_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k158_4_6_126 k h.1 (by omega)
theorem s158_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 4 7 = true := by decide +kernel
theorem s158_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 0 = true := by decide +kernel
theorem s158_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 1 = true := by decide +kernel
theorem s158_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 2 = true := by decide +kernel
theorem s158_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 3 = true := by decide +kernel
theorem s158_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 4 = true := by decide +kernel
theorem s158_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 5 = true := by decide +kernel
theorem k158_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k158_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k158_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k158_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k158_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k158_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k158_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s158_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k158_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k158_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k158_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k158_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k158_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k158_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 158) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (158 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k158_5_6_126 k h.1 (by omega)
theorem s158_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 5 7 = true := by decide +kernel
theorem s158_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 0 = true := by decide +kernel
theorem s158_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 1 = true := by decide +kernel
theorem s158_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 2 = true := by decide +kernel
theorem s158_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 3 = true := by decide +kernel
theorem s158_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 4 = true := by decide +kernel
theorem s158_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 5 = true := by decide +kernel
theorem s158_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 6 = true := by decide +kernel
theorem k158_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k158_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k158_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k158_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k158_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s158_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k158_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k158_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k158_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k158_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 158) ((InDA1.TCasaD 6 6 7).getD (158 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k158_6_7_12 k h.1 (by omega)
theorem col158_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 7 v) = true := by decide +kernel
theorem col158 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 158) 158 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col158_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col158_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col158_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s158_3_0
    · exact s158_3_1
    · exact s158_3_2
    · exact s158_3_3
    · exact s158_3_4
    · exact s158_3_5
    · exact s158_3_6
    · exact s158_3_7
  · fin_cases v
    · exact s158_4_0
    · exact s158_4_1
    · exact s158_4_2
    · exact s158_4_3
    · exact s158_4_4
    · exact s158_4_5
    · exact s158_4_6
    · exact s158_4_7
  · fin_cases v
    · exact s158_5_0
    · exact s158_5_1
    · exact s158_5_2
    · exact s158_5_3
    · exact s158_5_4
    · exact s158_5_5
    · exact s158_5_6
    · exact s158_5_7
  · fin_cases v
    · exact s158_6_0
    · exact s158_6_1
    · exact s158_6_2
    · exact s158_6_3
    · exact s158_6_4
    · exact s158_6_5
    · exact s158_6_6
    · exact s158_6_7
  · exact List.all_eq_true.mp col158_7 v (List.mem_finRange v)
theorem col159_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 0 v) = true := by decide +kernel
theorem col159_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 1 v) = true := by decide +kernel
theorem col159_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 2 v) = true := by decide +kernel
theorem s159_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 0 = true := by decide +kernel
theorem s159_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 1 = true := by decide +kernel
theorem s159_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 2 = true := by decide +kernel
theorem k159_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k159_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k159_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s159_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k159_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k159_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k159_3_3_26 k h.1 (by omega)
theorem s159_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 4 = true := by decide +kernel
theorem s159_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 5 = true := by decide +kernel
theorem k159_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k159_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k159_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k159_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k159_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k159_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k159_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k159_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k159_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k159_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k159_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s159_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k159_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k159_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k159_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k159_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k159_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k159_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k159_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k159_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k159_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k159_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k159_3_6_130 k h.1 (by omega)
theorem s159_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 3 7 = true := by decide +kernel
theorem s159_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 0 = true := by decide +kernel
theorem s159_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 1 = true := by decide +kernel
theorem s159_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 2 = true := by decide +kernel
theorem s159_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 3 = true := by decide +kernel
theorem s159_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 4 = true := by decide +kernel
theorem s159_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 5 = true := by decide +kernel
theorem k159_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k159_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k159_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k159_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k159_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k159_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k159_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s159_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k159_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k159_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k159_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k159_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k159_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k159_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k159_4_6_126 k h.1 (by omega)
theorem s159_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 4 7 = true := by decide +kernel
theorem s159_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 0 = true := by decide +kernel
theorem s159_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 1 = true := by decide +kernel
theorem s159_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 2 = true := by decide +kernel
theorem s159_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 3 = true := by decide +kernel
theorem s159_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 4 = true := by decide +kernel
theorem s159_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 5 = true := by decide +kernel
theorem k159_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k159_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k159_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k159_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k159_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k159_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k159_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s159_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k159_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k159_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k159_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k159_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k159_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k159_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 159) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (159 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k159_5_6_126 k h.1 (by omega)
theorem s159_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 5 7 = true := by decide +kernel
theorem s159_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 0 = true := by decide +kernel
theorem s159_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 1 = true := by decide +kernel
theorem s159_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 2 = true := by decide +kernel
theorem s159_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 3 = true := by decide +kernel
theorem s159_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 4 = true := by decide +kernel
theorem s159_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 5 = true := by decide +kernel
theorem s159_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 6 = true := by decide +kernel
theorem k159_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k159_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k159_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k159_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k159_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s159_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k159_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k159_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k159_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k159_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 159) ((InDA1.TCasaD 6 6 7).getD (159 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k159_6_7_12 k h.1 (by omega)
theorem col159_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 7 v) = true := by decide +kernel
theorem col159 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 159) 159 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col159_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col159_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col159_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s159_3_0
    · exact s159_3_1
    · exact s159_3_2
    · exact s159_3_3
    · exact s159_3_4
    · exact s159_3_5
    · exact s159_3_6
    · exact s159_3_7
  · fin_cases v
    · exact s159_4_0
    · exact s159_4_1
    · exact s159_4_2
    · exact s159_4_3
    · exact s159_4_4
    · exact s159_4_5
    · exact s159_4_6
    · exact s159_4_7
  · fin_cases v
    · exact s159_5_0
    · exact s159_5_1
    · exact s159_5_2
    · exact s159_5_3
    · exact s159_5_4
    · exact s159_5_5
    · exact s159_5_6
    · exact s159_5_7
  · fin_cases v
    · exact s159_6_0
    · exact s159_6_1
    · exact s159_6_2
    · exact s159_6_3
    · exact s159_6_4
    · exact s159_6_5
    · exact s159_6_6
    · exact s159_6_7
  · exact List.all_eq_true.mp col159_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
