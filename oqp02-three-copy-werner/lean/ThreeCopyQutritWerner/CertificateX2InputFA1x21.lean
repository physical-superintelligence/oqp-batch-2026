module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [105, 110). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col105_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 0 v) = true := by decide +kernel
theorem col105_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 1 v) = true := by decide +kernel
theorem col105_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 2 v) = true := by decide +kernel
theorem s105_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 0 = true := by decide +kernel
theorem s105_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 1 = true := by decide +kernel
theorem s105_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 2 = true := by decide +kernel
theorem k105_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k105_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k105_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s105_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k105_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k105_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k105_3_3_26 k h.1 (by omega)
theorem s105_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 4 = true := by decide +kernel
theorem s105_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 5 = true := by decide +kernel
theorem k105_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k105_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k105_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k105_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k105_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k105_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k105_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k105_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k105_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k105_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k105_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s105_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k105_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k105_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k105_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k105_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k105_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k105_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k105_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k105_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k105_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k105_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k105_3_6_130 k h.1 (by omega)
theorem s105_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 3 7 = true := by decide +kernel
theorem s105_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 0 = true := by decide +kernel
theorem s105_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 1 = true := by decide +kernel
theorem s105_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 2 = true := by decide +kernel
theorem s105_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 3 = true := by decide +kernel
theorem s105_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 4 = true := by decide +kernel
theorem s105_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 5 = true := by decide +kernel
theorem k105_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k105_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k105_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k105_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k105_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k105_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k105_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s105_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k105_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k105_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k105_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k105_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k105_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k105_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k105_4_6_126 k h.1 (by omega)
theorem s105_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 4 7 = true := by decide +kernel
theorem s105_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 0 = true := by decide +kernel
theorem s105_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 1 = true := by decide +kernel
theorem s105_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 2 = true := by decide +kernel
theorem s105_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 3 = true := by decide +kernel
theorem s105_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 4 = true := by decide +kernel
theorem s105_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 5 = true := by decide +kernel
theorem k105_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k105_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k105_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k105_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k105_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k105_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k105_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s105_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k105_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k105_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k105_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k105_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k105_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k105_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 105) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (105 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k105_5_6_126 k h.1 (by omega)
theorem s105_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 5 7 = true := by decide +kernel
theorem s105_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 0 = true := by decide +kernel
theorem s105_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 1 = true := by decide +kernel
theorem s105_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 2 = true := by decide +kernel
theorem s105_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 3 = true := by decide +kernel
theorem s105_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 4 = true := by decide +kernel
theorem s105_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 5 = true := by decide +kernel
theorem s105_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 6 = true := by decide +kernel
theorem k105_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k105_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k105_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k105_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k105_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s105_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k105_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k105_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k105_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k105_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 105) ((InDA1.TCasaD 6 6 7).getD (105 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k105_6_7_12 k h.1 (by omega)
theorem col105_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 7 v) = true := by decide +kernel
theorem col105 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 105) 105 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col105_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col105_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col105_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s105_6_0
    · exact s105_6_1
    · exact s105_6_2
    · exact s105_6_3
    · exact s105_6_4
    · exact s105_6_5
    · exact s105_6_6
    · exact s105_6_7
  · exact List.all_eq_true.mp col105_7 v (List.mem_finRange v)
theorem col106_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 0 v) = true := by decide +kernel
theorem col106_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 1 v) = true := by decide +kernel
theorem col106_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 2 v) = true := by decide +kernel
theorem s106_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 0 = true := by decide +kernel
theorem s106_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 1 = true := by decide +kernel
theorem s106_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 2 = true := by decide +kernel
theorem k106_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k106_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k106_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s106_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k106_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k106_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k106_3_3_26 k h.1 (by omega)
theorem s106_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 4 = true := by decide +kernel
theorem s106_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 5 = true := by decide +kernel
theorem k106_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k106_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k106_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k106_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k106_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k106_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k106_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k106_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k106_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k106_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k106_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s106_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k106_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k106_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k106_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k106_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k106_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k106_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k106_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k106_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k106_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k106_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k106_3_6_130 k h.1 (by omega)
theorem s106_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 3 7 = true := by decide +kernel
theorem s106_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 0 = true := by decide +kernel
theorem s106_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 1 = true := by decide +kernel
theorem s106_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 2 = true := by decide +kernel
theorem s106_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 3 = true := by decide +kernel
theorem s106_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 4 = true := by decide +kernel
theorem s106_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 5 = true := by decide +kernel
theorem k106_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k106_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k106_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k106_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k106_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k106_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k106_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s106_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k106_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k106_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k106_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k106_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k106_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k106_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k106_4_6_126 k h.1 (by omega)
theorem s106_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 4 7 = true := by decide +kernel
theorem s106_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 0 = true := by decide +kernel
theorem s106_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 1 = true := by decide +kernel
theorem s106_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 2 = true := by decide +kernel
theorem s106_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 3 = true := by decide +kernel
theorem s106_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 4 = true := by decide +kernel
theorem s106_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 5 = true := by decide +kernel
theorem k106_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k106_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k106_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k106_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k106_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k106_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k106_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s106_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k106_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k106_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k106_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k106_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k106_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k106_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 106) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (106 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k106_5_6_126 k h.1 (by omega)
theorem s106_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 5 7 = true := by decide +kernel
theorem s106_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 0 = true := by decide +kernel
theorem s106_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 1 = true := by decide +kernel
theorem s106_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 2 = true := by decide +kernel
theorem s106_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 3 = true := by decide +kernel
theorem s106_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 4 = true := by decide +kernel
theorem s106_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 5 = true := by decide +kernel
theorem s106_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 6 = true := by decide +kernel
theorem k106_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k106_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k106_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k106_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k106_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s106_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k106_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k106_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k106_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k106_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 106) ((InDA1.TCasaD 6 6 7).getD (106 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k106_6_7_12 k h.1 (by omega)
theorem col106_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 7 v) = true := by decide +kernel
theorem col106 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 106) 106 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col106_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col106_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col106_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s106_6_0
    · exact s106_6_1
    · exact s106_6_2
    · exact s106_6_3
    · exact s106_6_4
    · exact s106_6_5
    · exact s106_6_6
    · exact s106_6_7
  · exact List.all_eq_true.mp col106_7 v (List.mem_finRange v)
theorem col107_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 0 v) = true := by decide +kernel
theorem col107_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 1 v) = true := by decide +kernel
theorem col107_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 2 v) = true := by decide +kernel
theorem s107_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 0 = true := by decide +kernel
theorem s107_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 1 = true := by decide +kernel
theorem s107_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 2 = true := by decide +kernel
theorem k107_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k107_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k107_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s107_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k107_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k107_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k107_3_3_26 k h.1 (by omega)
theorem s107_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 4 = true := by decide +kernel
theorem s107_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 5 = true := by decide +kernel
theorem k107_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k107_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k107_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k107_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k107_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k107_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k107_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k107_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k107_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k107_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k107_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s107_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k107_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k107_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k107_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k107_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k107_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k107_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k107_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k107_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k107_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k107_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k107_3_6_130 k h.1 (by omega)
theorem s107_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 3 7 = true := by decide +kernel
theorem s107_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 0 = true := by decide +kernel
theorem s107_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 1 = true := by decide +kernel
theorem s107_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 2 = true := by decide +kernel
theorem s107_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 3 = true := by decide +kernel
theorem s107_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 4 = true := by decide +kernel
theorem s107_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 5 = true := by decide +kernel
theorem k107_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k107_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k107_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k107_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k107_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k107_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k107_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s107_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k107_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k107_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k107_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k107_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k107_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k107_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k107_4_6_126 k h.1 (by omega)
theorem s107_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 4 7 = true := by decide +kernel
theorem s107_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 0 = true := by decide +kernel
theorem s107_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 1 = true := by decide +kernel
theorem s107_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 2 = true := by decide +kernel
theorem s107_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 3 = true := by decide +kernel
theorem s107_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 4 = true := by decide +kernel
theorem s107_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 5 = true := by decide +kernel
theorem k107_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k107_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k107_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k107_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k107_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k107_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k107_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s107_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k107_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k107_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k107_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k107_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k107_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k107_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 107) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (107 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k107_5_6_126 k h.1 (by omega)
theorem s107_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 5 7 = true := by decide +kernel
theorem s107_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 0 = true := by decide +kernel
theorem s107_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 1 = true := by decide +kernel
theorem s107_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 2 = true := by decide +kernel
theorem s107_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 3 = true := by decide +kernel
theorem s107_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 4 = true := by decide +kernel
theorem s107_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 5 = true := by decide +kernel
theorem s107_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 6 = true := by decide +kernel
theorem k107_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k107_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k107_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k107_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k107_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s107_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k107_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k107_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k107_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k107_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 107) ((InDA1.TCasaD 6 6 7).getD (107 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k107_6_7_12 k h.1 (by omega)
theorem col107_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 7 v) = true := by decide +kernel
theorem col107 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 107) 107 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col107_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col107_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col107_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s107_6_0
    · exact s107_6_1
    · exact s107_6_2
    · exact s107_6_3
    · exact s107_6_4
    · exact s107_6_5
    · exact s107_6_6
    · exact s107_6_7
  · exact List.all_eq_true.mp col107_7 v (List.mem_finRange v)
theorem col108_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 0 v) = true := by decide +kernel
theorem col108_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 1 v) = true := by decide +kernel
theorem col108_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 2 v) = true := by decide +kernel
theorem s108_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 0 = true := by decide +kernel
theorem s108_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 1 = true := by decide +kernel
theorem s108_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 2 = true := by decide +kernel
theorem k108_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k108_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k108_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s108_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k108_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k108_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k108_3_3_26 k h.1 (by omega)
theorem s108_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 4 = true := by decide +kernel
theorem s108_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 5 = true := by decide +kernel
theorem k108_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k108_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k108_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k108_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k108_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k108_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k108_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k108_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k108_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k108_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k108_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s108_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k108_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k108_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k108_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k108_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k108_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k108_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k108_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k108_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k108_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k108_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k108_3_6_130 k h.1 (by omega)
theorem s108_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 3 7 = true := by decide +kernel
theorem s108_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 0 = true := by decide +kernel
theorem s108_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 1 = true := by decide +kernel
theorem s108_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 2 = true := by decide +kernel
theorem s108_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 3 = true := by decide +kernel
theorem s108_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 4 = true := by decide +kernel
theorem s108_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 5 = true := by decide +kernel
theorem k108_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k108_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k108_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k108_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k108_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k108_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k108_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s108_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k108_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k108_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k108_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k108_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k108_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k108_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k108_4_6_126 k h.1 (by omega)
theorem s108_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 4 7 = true := by decide +kernel
theorem s108_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 0 = true := by decide +kernel
theorem s108_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 1 = true := by decide +kernel
theorem s108_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 2 = true := by decide +kernel
theorem s108_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 3 = true := by decide +kernel
theorem s108_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 4 = true := by decide +kernel
theorem s108_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 5 = true := by decide +kernel
theorem k108_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k108_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k108_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k108_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k108_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k108_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k108_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s108_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k108_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k108_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k108_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k108_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k108_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k108_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 108) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (108 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k108_5_6_126 k h.1 (by omega)
theorem s108_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 5 7 = true := by decide +kernel
theorem s108_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 0 = true := by decide +kernel
theorem s108_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 1 = true := by decide +kernel
theorem s108_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 2 = true := by decide +kernel
theorem s108_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 3 = true := by decide +kernel
theorem s108_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 4 = true := by decide +kernel
theorem s108_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 5 = true := by decide +kernel
theorem s108_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 6 = true := by decide +kernel
theorem k108_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k108_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k108_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k108_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k108_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s108_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k108_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k108_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k108_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k108_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 108) ((InDA1.TCasaD 6 6 7).getD (108 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k108_6_7_12 k h.1 (by omega)
theorem col108_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 7 v) = true := by decide +kernel
theorem col108 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 108) 108 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col108_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col108_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col108_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s108_6_0
    · exact s108_6_1
    · exact s108_6_2
    · exact s108_6_3
    · exact s108_6_4
    · exact s108_6_5
    · exact s108_6_6
    · exact s108_6_7
  · exact List.all_eq_true.mp col108_7 v (List.mem_finRange v)
theorem col109_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 0 v) = true := by decide +kernel
theorem col109_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 1 v) = true := by decide +kernel
theorem col109_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 2 v) = true := by decide +kernel
theorem s109_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 0 = true := by decide +kernel
theorem s109_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 1 = true := by decide +kernel
theorem s109_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 2 = true := by decide +kernel
theorem k109_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k109_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k109_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s109_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k109_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k109_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k109_3_3_26 k h.1 (by omega)
theorem s109_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 4 = true := by decide +kernel
theorem s109_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 5 = true := by decide +kernel
theorem k109_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k109_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k109_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k109_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k109_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k109_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k109_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k109_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k109_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k109_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k109_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s109_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k109_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k109_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k109_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k109_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k109_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k109_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k109_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k109_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k109_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k109_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k109_3_6_130 k h.1 (by omega)
theorem s109_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 3 7 = true := by decide +kernel
theorem s109_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 0 = true := by decide +kernel
theorem s109_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 1 = true := by decide +kernel
theorem s109_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 2 = true := by decide +kernel
theorem s109_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 3 = true := by decide +kernel
theorem s109_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 4 = true := by decide +kernel
theorem s109_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 5 = true := by decide +kernel
theorem k109_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k109_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k109_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k109_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k109_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k109_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k109_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s109_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k109_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k109_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k109_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k109_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k109_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k109_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k109_4_6_126 k h.1 (by omega)
theorem s109_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 4 7 = true := by decide +kernel
theorem s109_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 0 = true := by decide +kernel
theorem s109_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 1 = true := by decide +kernel
theorem s109_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 2 = true := by decide +kernel
theorem s109_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 3 = true := by decide +kernel
theorem s109_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 4 = true := by decide +kernel
theorem s109_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 5 = true := by decide +kernel
theorem k109_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k109_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k109_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k109_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k109_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k109_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k109_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s109_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k109_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k109_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k109_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k109_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k109_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k109_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 109) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (109 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k109_5_6_126 k h.1 (by omega)
theorem s109_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 5 7 = true := by decide +kernel
theorem s109_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 0 = true := by decide +kernel
theorem s109_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 1 = true := by decide +kernel
theorem s109_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 2 = true := by decide +kernel
theorem s109_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 3 = true := by decide +kernel
theorem s109_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 4 = true := by decide +kernel
theorem s109_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 5 = true := by decide +kernel
theorem s109_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 6 = true := by decide +kernel
theorem k109_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k109_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k109_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k109_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k109_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s109_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k109_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k109_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k109_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k109_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 109) ((InDA1.TCasaD 6 6 7).getD (109 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k109_6_7_12 k h.1 (by omega)
theorem col109_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 7 v) = true := by decide +kernel
theorem col109 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 109) 109 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col109_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col109_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col109_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s109_6_0
    · exact s109_6_1
    · exact s109_6_2
    · exact s109_6_3
    · exact s109_6_4
    · exact s109_6_5
    · exact s109_6_6
    · exact s109_6_7
  · exact List.all_eq_true.mp col109_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
