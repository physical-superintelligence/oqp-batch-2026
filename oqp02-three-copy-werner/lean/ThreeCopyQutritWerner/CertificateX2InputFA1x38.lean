module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [190, 195). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col190_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 0 v) = true := by decide +kernel
theorem col190_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 1 v) = true := by decide +kernel
theorem col190_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 2 v) = true := by decide +kernel
theorem s190_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 0 = true := by decide +kernel
theorem s190_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 1 = true := by decide +kernel
theorem s190_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 2 = true := by decide +kernel
theorem k190_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k190_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k190_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s190_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k190_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k190_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k190_3_3_26 k h.1 (by omega)
theorem s190_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 4 = true := by decide +kernel
theorem s190_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 5 = true := by decide +kernel
theorem k190_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k190_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k190_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k190_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k190_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k190_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k190_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k190_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k190_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k190_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k190_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s190_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k190_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k190_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k190_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k190_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k190_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k190_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k190_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k190_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k190_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k190_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k190_3_6_130 k h.1 (by omega)
theorem s190_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 3 7 = true := by decide +kernel
theorem s190_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 0 = true := by decide +kernel
theorem s190_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 1 = true := by decide +kernel
theorem s190_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 2 = true := by decide +kernel
theorem s190_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 3 = true := by decide +kernel
theorem s190_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 4 = true := by decide +kernel
theorem s190_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 5 = true := by decide +kernel
theorem k190_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k190_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k190_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k190_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k190_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k190_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k190_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s190_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k190_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k190_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k190_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k190_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k190_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k190_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k190_4_6_126 k h.1 (by omega)
theorem s190_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 4 7 = true := by decide +kernel
theorem s190_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 0 = true := by decide +kernel
theorem s190_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 1 = true := by decide +kernel
theorem s190_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 2 = true := by decide +kernel
theorem s190_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 3 = true := by decide +kernel
theorem s190_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 4 = true := by decide +kernel
theorem s190_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 5 = true := by decide +kernel
theorem k190_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k190_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k190_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k190_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k190_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k190_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k190_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s190_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k190_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k190_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k190_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k190_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k190_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k190_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 190) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (190 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k190_5_6_126 k h.1 (by omega)
theorem s190_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 5 7 = true := by decide +kernel
theorem s190_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 0 = true := by decide +kernel
theorem s190_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 1 = true := by decide +kernel
theorem s190_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 2 = true := by decide +kernel
theorem s190_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 3 = true := by decide +kernel
theorem s190_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 4 = true := by decide +kernel
theorem s190_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 5 = true := by decide +kernel
theorem s190_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 6 = true := by decide +kernel
theorem k190_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k190_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k190_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k190_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k190_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s190_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k190_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k190_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k190_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k190_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 190) ((InDA1.TCasaD 6 6 7).getD (190 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k190_6_7_12 k h.1 (by omega)
theorem col190_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 7 v) = true := by decide +kernel
theorem col190 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 190) 190 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col190_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col190_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col190_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s190_3_0
    · exact s190_3_1
    · exact s190_3_2
    · exact s190_3_3
    · exact s190_3_4
    · exact s190_3_5
    · exact s190_3_6
    · exact s190_3_7
  · fin_cases v
    · exact s190_4_0
    · exact s190_4_1
    · exact s190_4_2
    · exact s190_4_3
    · exact s190_4_4
    · exact s190_4_5
    · exact s190_4_6
    · exact s190_4_7
  · fin_cases v
    · exact s190_5_0
    · exact s190_5_1
    · exact s190_5_2
    · exact s190_5_3
    · exact s190_5_4
    · exact s190_5_5
    · exact s190_5_6
    · exact s190_5_7
  · fin_cases v
    · exact s190_6_0
    · exact s190_6_1
    · exact s190_6_2
    · exact s190_6_3
    · exact s190_6_4
    · exact s190_6_5
    · exact s190_6_6
    · exact s190_6_7
  · exact List.all_eq_true.mp col190_7 v (List.mem_finRange v)
theorem col191_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 0 v) = true := by decide +kernel
theorem col191_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 1 v) = true := by decide +kernel
theorem col191_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 2 v) = true := by decide +kernel
theorem s191_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 0 = true := by decide +kernel
theorem s191_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 1 = true := by decide +kernel
theorem s191_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 2 = true := by decide +kernel
theorem k191_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k191_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k191_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s191_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k191_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k191_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k191_3_3_26 k h.1 (by omega)
theorem s191_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 4 = true := by decide +kernel
theorem s191_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 5 = true := by decide +kernel
theorem k191_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k191_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k191_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k191_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k191_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k191_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k191_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k191_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k191_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k191_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k191_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s191_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k191_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k191_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k191_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k191_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k191_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k191_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k191_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k191_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k191_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k191_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k191_3_6_130 k h.1 (by omega)
theorem s191_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 3 7 = true := by decide +kernel
theorem s191_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 0 = true := by decide +kernel
theorem s191_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 1 = true := by decide +kernel
theorem s191_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 2 = true := by decide +kernel
theorem s191_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 3 = true := by decide +kernel
theorem s191_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 4 = true := by decide +kernel
theorem s191_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 5 = true := by decide +kernel
theorem k191_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k191_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k191_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k191_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k191_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k191_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k191_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s191_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k191_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k191_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k191_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k191_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k191_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k191_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k191_4_6_126 k h.1 (by omega)
theorem s191_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 4 7 = true := by decide +kernel
theorem s191_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 0 = true := by decide +kernel
theorem s191_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 1 = true := by decide +kernel
theorem s191_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 2 = true := by decide +kernel
theorem s191_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 3 = true := by decide +kernel
theorem s191_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 4 = true := by decide +kernel
theorem s191_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 5 = true := by decide +kernel
theorem k191_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k191_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k191_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k191_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k191_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k191_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k191_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s191_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k191_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k191_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k191_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k191_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k191_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k191_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 191) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (191 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k191_5_6_126 k h.1 (by omega)
theorem s191_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 5 7 = true := by decide +kernel
theorem s191_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 0 = true := by decide +kernel
theorem s191_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 1 = true := by decide +kernel
theorem s191_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 2 = true := by decide +kernel
theorem s191_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 3 = true := by decide +kernel
theorem s191_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 4 = true := by decide +kernel
theorem s191_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 5 = true := by decide +kernel
theorem s191_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 6 = true := by decide +kernel
theorem k191_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k191_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k191_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k191_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k191_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s191_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k191_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k191_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k191_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k191_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 191) ((InDA1.TCasaD 6 6 7).getD (191 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k191_6_7_12 k h.1 (by omega)
theorem col191_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 7 v) = true := by decide +kernel
theorem col191 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 191) 191 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col191_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col191_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col191_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s191_3_0
    · exact s191_3_1
    · exact s191_3_2
    · exact s191_3_3
    · exact s191_3_4
    · exact s191_3_5
    · exact s191_3_6
    · exact s191_3_7
  · fin_cases v
    · exact s191_4_0
    · exact s191_4_1
    · exact s191_4_2
    · exact s191_4_3
    · exact s191_4_4
    · exact s191_4_5
    · exact s191_4_6
    · exact s191_4_7
  · fin_cases v
    · exact s191_5_0
    · exact s191_5_1
    · exact s191_5_2
    · exact s191_5_3
    · exact s191_5_4
    · exact s191_5_5
    · exact s191_5_6
    · exact s191_5_7
  · fin_cases v
    · exact s191_6_0
    · exact s191_6_1
    · exact s191_6_2
    · exact s191_6_3
    · exact s191_6_4
    · exact s191_6_5
    · exact s191_6_6
    · exact s191_6_7
  · exact List.all_eq_true.mp col191_7 v (List.mem_finRange v)
theorem col192_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 0 v) = true := by decide +kernel
theorem col192_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 1 v) = true := by decide +kernel
theorem col192_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 2 v) = true := by decide +kernel
theorem s192_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 0 = true := by decide +kernel
theorem s192_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 1 = true := by decide +kernel
theorem s192_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 2 = true := by decide +kernel
theorem k192_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k192_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k192_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s192_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k192_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k192_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k192_3_3_26 k h.1 (by omega)
theorem s192_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 4 = true := by decide +kernel
theorem s192_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 5 = true := by decide +kernel
theorem k192_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k192_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k192_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k192_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k192_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k192_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k192_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k192_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k192_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k192_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k192_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s192_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k192_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k192_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k192_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k192_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k192_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k192_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k192_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k192_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k192_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k192_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k192_3_6_130 k h.1 (by omega)
theorem s192_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 3 7 = true := by decide +kernel
theorem s192_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 0 = true := by decide +kernel
theorem s192_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 1 = true := by decide +kernel
theorem s192_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 2 = true := by decide +kernel
theorem s192_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 3 = true := by decide +kernel
theorem s192_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 4 = true := by decide +kernel
theorem s192_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 5 = true := by decide +kernel
theorem k192_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k192_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k192_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k192_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k192_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k192_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k192_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s192_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k192_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k192_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k192_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k192_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k192_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k192_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k192_4_6_126 k h.1 (by omega)
theorem s192_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 4 7 = true := by decide +kernel
theorem s192_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 0 = true := by decide +kernel
theorem s192_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 1 = true := by decide +kernel
theorem s192_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 2 = true := by decide +kernel
theorem s192_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 3 = true := by decide +kernel
theorem s192_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 4 = true := by decide +kernel
theorem s192_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 5 = true := by decide +kernel
theorem k192_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k192_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k192_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k192_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k192_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k192_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k192_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s192_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k192_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k192_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k192_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k192_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k192_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k192_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 192) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (192 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k192_5_6_126 k h.1 (by omega)
theorem s192_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 5 7 = true := by decide +kernel
theorem s192_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 0 = true := by decide +kernel
theorem s192_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 1 = true := by decide +kernel
theorem s192_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 2 = true := by decide +kernel
theorem s192_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 3 = true := by decide +kernel
theorem s192_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 4 = true := by decide +kernel
theorem s192_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 5 = true := by decide +kernel
theorem s192_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 6 = true := by decide +kernel
theorem k192_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k192_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k192_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k192_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k192_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s192_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k192_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k192_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k192_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k192_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 192) ((InDA1.TCasaD 6 6 7).getD (192 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k192_6_7_12 k h.1 (by omega)
theorem col192_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 7 v) = true := by decide +kernel
theorem col192 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 192) 192 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col192_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col192_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col192_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s192_3_0
    · exact s192_3_1
    · exact s192_3_2
    · exact s192_3_3
    · exact s192_3_4
    · exact s192_3_5
    · exact s192_3_6
    · exact s192_3_7
  · fin_cases v
    · exact s192_4_0
    · exact s192_4_1
    · exact s192_4_2
    · exact s192_4_3
    · exact s192_4_4
    · exact s192_4_5
    · exact s192_4_6
    · exact s192_4_7
  · fin_cases v
    · exact s192_5_0
    · exact s192_5_1
    · exact s192_5_2
    · exact s192_5_3
    · exact s192_5_4
    · exact s192_5_5
    · exact s192_5_6
    · exact s192_5_7
  · fin_cases v
    · exact s192_6_0
    · exact s192_6_1
    · exact s192_6_2
    · exact s192_6_3
    · exact s192_6_4
    · exact s192_6_5
    · exact s192_6_6
    · exact s192_6_7
  · exact List.all_eq_true.mp col192_7 v (List.mem_finRange v)
theorem col193_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 0 v) = true := by decide +kernel
theorem col193_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 1 v) = true := by decide +kernel
theorem col193_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 2 v) = true := by decide +kernel
theorem s193_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 0 = true := by decide +kernel
theorem s193_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 1 = true := by decide +kernel
theorem s193_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 2 = true := by decide +kernel
theorem k193_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k193_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k193_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s193_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k193_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k193_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k193_3_3_26 k h.1 (by omega)
theorem s193_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 4 = true := by decide +kernel
theorem s193_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 5 = true := by decide +kernel
theorem k193_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k193_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k193_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k193_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k193_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k193_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k193_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k193_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k193_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k193_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k193_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s193_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k193_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k193_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k193_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k193_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k193_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k193_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k193_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k193_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k193_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k193_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k193_3_6_130 k h.1 (by omega)
theorem s193_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 3 7 = true := by decide +kernel
theorem s193_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 0 = true := by decide +kernel
theorem s193_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 1 = true := by decide +kernel
theorem s193_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 2 = true := by decide +kernel
theorem s193_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 3 = true := by decide +kernel
theorem s193_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 4 = true := by decide +kernel
theorem s193_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 5 = true := by decide +kernel
theorem k193_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k193_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k193_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k193_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k193_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k193_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k193_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s193_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k193_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k193_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k193_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k193_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k193_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k193_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k193_4_6_126 k h.1 (by omega)
theorem s193_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 4 7 = true := by decide +kernel
theorem s193_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 0 = true := by decide +kernel
theorem s193_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 1 = true := by decide +kernel
theorem s193_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 2 = true := by decide +kernel
theorem s193_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 3 = true := by decide +kernel
theorem s193_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 4 = true := by decide +kernel
theorem s193_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 5 = true := by decide +kernel
theorem k193_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k193_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k193_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k193_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k193_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k193_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k193_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s193_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k193_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k193_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k193_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k193_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k193_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k193_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 193) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (193 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k193_5_6_126 k h.1 (by omega)
theorem s193_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 5 7 = true := by decide +kernel
theorem s193_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 0 = true := by decide +kernel
theorem s193_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 1 = true := by decide +kernel
theorem s193_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 2 = true := by decide +kernel
theorem s193_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 3 = true := by decide +kernel
theorem s193_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 4 = true := by decide +kernel
theorem s193_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 5 = true := by decide +kernel
theorem s193_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 6 = true := by decide +kernel
theorem k193_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k193_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k193_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k193_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k193_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s193_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k193_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k193_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k193_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k193_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 193) ((InDA1.TCasaD 6 6 7).getD (193 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k193_6_7_12 k h.1 (by omega)
theorem col193_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 7 v) = true := by decide +kernel
theorem col193 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 193) 193 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col193_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col193_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col193_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s193_3_0
    · exact s193_3_1
    · exact s193_3_2
    · exact s193_3_3
    · exact s193_3_4
    · exact s193_3_5
    · exact s193_3_6
    · exact s193_3_7
  · fin_cases v
    · exact s193_4_0
    · exact s193_4_1
    · exact s193_4_2
    · exact s193_4_3
    · exact s193_4_4
    · exact s193_4_5
    · exact s193_4_6
    · exact s193_4_7
  · fin_cases v
    · exact s193_5_0
    · exact s193_5_1
    · exact s193_5_2
    · exact s193_5_3
    · exact s193_5_4
    · exact s193_5_5
    · exact s193_5_6
    · exact s193_5_7
  · fin_cases v
    · exact s193_6_0
    · exact s193_6_1
    · exact s193_6_2
    · exact s193_6_3
    · exact s193_6_4
    · exact s193_6_5
    · exact s193_6_6
    · exact s193_6_7
  · exact List.all_eq_true.mp col193_7 v (List.mem_finRange v)
theorem col194_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 0 v) = true := by decide +kernel
theorem col194_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 1 v) = true := by decide +kernel
theorem col194_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 2 v) = true := by decide +kernel
theorem s194_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 0 = true := by decide +kernel
theorem s194_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 1 = true := by decide +kernel
theorem s194_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 2 = true := by decide +kernel
theorem k194_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k194_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k194_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s194_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k194_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k194_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k194_3_3_26 k h.1 (by omega)
theorem s194_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 4 = true := by decide +kernel
theorem s194_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 5 = true := by decide +kernel
theorem k194_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k194_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k194_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k194_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k194_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k194_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k194_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k194_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k194_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k194_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k194_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s194_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k194_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k194_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k194_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k194_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k194_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k194_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k194_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k194_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k194_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k194_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k194_3_6_130 k h.1 (by omega)
theorem s194_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 3 7 = true := by decide +kernel
theorem s194_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 0 = true := by decide +kernel
theorem s194_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 1 = true := by decide +kernel
theorem s194_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 2 = true := by decide +kernel
theorem s194_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 3 = true := by decide +kernel
theorem s194_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 4 = true := by decide +kernel
theorem s194_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 5 = true := by decide +kernel
theorem k194_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k194_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k194_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k194_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k194_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k194_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k194_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s194_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k194_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k194_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k194_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k194_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k194_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k194_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k194_4_6_126 k h.1 (by omega)
theorem s194_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 4 7 = true := by decide +kernel
theorem s194_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 0 = true := by decide +kernel
theorem s194_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 1 = true := by decide +kernel
theorem s194_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 2 = true := by decide +kernel
theorem s194_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 3 = true := by decide +kernel
theorem s194_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 4 = true := by decide +kernel
theorem s194_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 5 = true := by decide +kernel
theorem k194_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k194_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k194_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k194_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k194_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k194_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k194_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s194_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k194_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k194_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k194_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k194_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k194_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k194_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 194) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (194 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k194_5_6_126 k h.1 (by omega)
theorem s194_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 5 7 = true := by decide +kernel
theorem s194_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 0 = true := by decide +kernel
theorem s194_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 1 = true := by decide +kernel
theorem s194_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 2 = true := by decide +kernel
theorem s194_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 3 = true := by decide +kernel
theorem s194_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 4 = true := by decide +kernel
theorem s194_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 5 = true := by decide +kernel
theorem s194_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 6 = true := by decide +kernel
theorem k194_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k194_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k194_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k194_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k194_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s194_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k194_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k194_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k194_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k194_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 194) ((InDA1.TCasaD 6 6 7).getD (194 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k194_6_7_12 k h.1 (by omega)
theorem col194_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 7 v) = true := by decide +kernel
theorem col194 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 194) 194 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col194_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col194_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col194_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s194_3_0
    · exact s194_3_1
    · exact s194_3_2
    · exact s194_3_3
    · exact s194_3_4
    · exact s194_3_5
    · exact s194_3_6
    · exact s194_3_7
  · fin_cases v
    · exact s194_4_0
    · exact s194_4_1
    · exact s194_4_2
    · exact s194_4_3
    · exact s194_4_4
    · exact s194_4_5
    · exact s194_4_6
    · exact s194_4_7
  · fin_cases v
    · exact s194_5_0
    · exact s194_5_1
    · exact s194_5_2
    · exact s194_5_3
    · exact s194_5_4
    · exact s194_5_5
    · exact s194_5_6
    · exact s194_5_7
  · fin_cases v
    · exact s194_6_0
    · exact s194_6_1
    · exact s194_6_2
    · exact s194_6_3
    · exact s194_6_4
    · exact s194_6_5
    · exact s194_6_6
    · exact s194_6_7
  · exact List.all_eq_true.mp col194_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
