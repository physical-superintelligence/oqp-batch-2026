module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [195, 200). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col195_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 0 v) = true := by decide +kernel
theorem col195_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 1 v) = true := by decide +kernel
theorem col195_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 2 v) = true := by decide +kernel
theorem s195_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 0 = true := by decide +kernel
theorem s195_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 1 = true := by decide +kernel
theorem s195_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 2 = true := by decide +kernel
theorem k195_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k195_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k195_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s195_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k195_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k195_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k195_3_3_26 k h.1 (by omega)
theorem s195_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 4 = true := by decide +kernel
theorem s195_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 5 = true := by decide +kernel
theorem k195_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k195_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k195_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k195_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k195_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k195_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k195_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k195_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k195_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k195_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k195_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s195_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k195_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k195_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k195_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k195_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k195_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k195_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k195_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k195_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k195_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k195_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k195_3_6_130 k h.1 (by omega)
theorem s195_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 3 7 = true := by decide +kernel
theorem s195_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 0 = true := by decide +kernel
theorem s195_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 1 = true := by decide +kernel
theorem s195_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 2 = true := by decide +kernel
theorem s195_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 3 = true := by decide +kernel
theorem s195_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 4 = true := by decide +kernel
theorem s195_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 5 = true := by decide +kernel
theorem k195_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k195_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k195_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k195_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k195_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k195_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k195_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s195_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k195_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k195_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k195_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k195_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k195_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k195_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k195_4_6_126 k h.1 (by omega)
theorem s195_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 4 7 = true := by decide +kernel
theorem s195_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 0 = true := by decide +kernel
theorem s195_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 1 = true := by decide +kernel
theorem s195_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 2 = true := by decide +kernel
theorem s195_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 3 = true := by decide +kernel
theorem s195_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 4 = true := by decide +kernel
theorem s195_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 5 = true := by decide +kernel
theorem k195_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k195_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k195_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k195_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k195_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k195_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k195_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s195_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k195_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k195_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k195_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k195_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k195_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k195_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 195) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (195 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k195_5_6_126 k h.1 (by omega)
theorem s195_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 5 7 = true := by decide +kernel
theorem s195_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 0 = true := by decide +kernel
theorem s195_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 1 = true := by decide +kernel
theorem s195_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 2 = true := by decide +kernel
theorem s195_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 3 = true := by decide +kernel
theorem s195_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 4 = true := by decide +kernel
theorem s195_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 5 = true := by decide +kernel
theorem s195_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 6 = true := by decide +kernel
theorem k195_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k195_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k195_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k195_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k195_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s195_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k195_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k195_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k195_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k195_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 195) ((InDA1.TCasaD 6 6 7).getD (195 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k195_6_7_12 k h.1 (by omega)
theorem col195_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 7 v) = true := by decide +kernel
theorem col195 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 195) 195 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col195_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col195_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col195_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s195_3_0
    · exact s195_3_1
    · exact s195_3_2
    · exact s195_3_3
    · exact s195_3_4
    · exact s195_3_5
    · exact s195_3_6
    · exact s195_3_7
  · fin_cases v
    · exact s195_4_0
    · exact s195_4_1
    · exact s195_4_2
    · exact s195_4_3
    · exact s195_4_4
    · exact s195_4_5
    · exact s195_4_6
    · exact s195_4_7
  · fin_cases v
    · exact s195_5_0
    · exact s195_5_1
    · exact s195_5_2
    · exact s195_5_3
    · exact s195_5_4
    · exact s195_5_5
    · exact s195_5_6
    · exact s195_5_7
  · fin_cases v
    · exact s195_6_0
    · exact s195_6_1
    · exact s195_6_2
    · exact s195_6_3
    · exact s195_6_4
    · exact s195_6_5
    · exact s195_6_6
    · exact s195_6_7
  · exact List.all_eq_true.mp col195_7 v (List.mem_finRange v)
theorem col196_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 0 v) = true := by decide +kernel
theorem col196_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 1 v) = true := by decide +kernel
theorem col196_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 2 v) = true := by decide +kernel
theorem s196_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 0 = true := by decide +kernel
theorem s196_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 1 = true := by decide +kernel
theorem s196_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 2 = true := by decide +kernel
theorem k196_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k196_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k196_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s196_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k196_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k196_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k196_3_3_26 k h.1 (by omega)
theorem s196_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 4 = true := by decide +kernel
theorem s196_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 5 = true := by decide +kernel
theorem k196_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k196_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k196_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k196_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k196_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k196_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k196_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k196_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k196_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k196_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k196_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s196_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k196_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k196_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k196_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k196_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k196_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k196_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k196_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k196_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k196_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k196_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k196_3_6_130 k h.1 (by omega)
theorem s196_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 3 7 = true := by decide +kernel
theorem s196_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 0 = true := by decide +kernel
theorem s196_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 1 = true := by decide +kernel
theorem s196_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 2 = true := by decide +kernel
theorem s196_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 3 = true := by decide +kernel
theorem s196_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 4 = true := by decide +kernel
theorem s196_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 5 = true := by decide +kernel
theorem k196_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k196_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k196_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k196_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k196_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k196_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k196_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s196_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k196_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k196_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k196_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k196_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k196_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k196_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k196_4_6_126 k h.1 (by omega)
theorem s196_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 4 7 = true := by decide +kernel
theorem s196_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 0 = true := by decide +kernel
theorem s196_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 1 = true := by decide +kernel
theorem s196_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 2 = true := by decide +kernel
theorem s196_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 3 = true := by decide +kernel
theorem s196_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 4 = true := by decide +kernel
theorem s196_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 5 = true := by decide +kernel
theorem k196_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k196_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k196_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k196_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k196_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k196_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k196_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s196_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k196_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k196_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k196_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k196_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k196_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k196_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 196) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (196 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k196_5_6_126 k h.1 (by omega)
theorem s196_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 5 7 = true := by decide +kernel
theorem s196_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 0 = true := by decide +kernel
theorem s196_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 1 = true := by decide +kernel
theorem s196_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 2 = true := by decide +kernel
theorem s196_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 3 = true := by decide +kernel
theorem s196_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 4 = true := by decide +kernel
theorem s196_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 5 = true := by decide +kernel
theorem s196_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 6 = true := by decide +kernel
theorem k196_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k196_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k196_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k196_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k196_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s196_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k196_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k196_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k196_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k196_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 196) ((InDA1.TCasaD 6 6 7).getD (196 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k196_6_7_12 k h.1 (by omega)
theorem col196_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 7 v) = true := by decide +kernel
theorem col196 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 196) 196 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col196_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col196_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col196_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s196_3_0
    · exact s196_3_1
    · exact s196_3_2
    · exact s196_3_3
    · exact s196_3_4
    · exact s196_3_5
    · exact s196_3_6
    · exact s196_3_7
  · fin_cases v
    · exact s196_4_0
    · exact s196_4_1
    · exact s196_4_2
    · exact s196_4_3
    · exact s196_4_4
    · exact s196_4_5
    · exact s196_4_6
    · exact s196_4_7
  · fin_cases v
    · exact s196_5_0
    · exact s196_5_1
    · exact s196_5_2
    · exact s196_5_3
    · exact s196_5_4
    · exact s196_5_5
    · exact s196_5_6
    · exact s196_5_7
  · fin_cases v
    · exact s196_6_0
    · exact s196_6_1
    · exact s196_6_2
    · exact s196_6_3
    · exact s196_6_4
    · exact s196_6_5
    · exact s196_6_6
    · exact s196_6_7
  · exact List.all_eq_true.mp col196_7 v (List.mem_finRange v)
theorem col197_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 0 v) = true := by decide +kernel
theorem col197_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 1 v) = true := by decide +kernel
theorem col197_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 2 v) = true := by decide +kernel
theorem s197_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 0 = true := by decide +kernel
theorem s197_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 1 = true := by decide +kernel
theorem s197_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 2 = true := by decide +kernel
theorem k197_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k197_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k197_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s197_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k197_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k197_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k197_3_3_26 k h.1 (by omega)
theorem s197_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 4 = true := by decide +kernel
theorem s197_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 5 = true := by decide +kernel
theorem k197_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k197_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k197_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k197_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k197_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k197_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k197_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k197_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k197_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k197_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k197_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s197_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k197_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k197_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k197_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k197_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k197_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k197_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k197_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k197_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k197_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k197_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k197_3_6_130 k h.1 (by omega)
theorem s197_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 3 7 = true := by decide +kernel
theorem s197_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 0 = true := by decide +kernel
theorem s197_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 1 = true := by decide +kernel
theorem s197_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 2 = true := by decide +kernel
theorem s197_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 3 = true := by decide +kernel
theorem s197_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 4 = true := by decide +kernel
theorem s197_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 5 = true := by decide +kernel
theorem k197_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k197_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k197_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k197_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k197_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k197_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k197_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s197_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k197_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k197_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k197_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k197_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k197_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k197_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k197_4_6_126 k h.1 (by omega)
theorem s197_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 4 7 = true := by decide +kernel
theorem s197_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 0 = true := by decide +kernel
theorem s197_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 1 = true := by decide +kernel
theorem s197_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 2 = true := by decide +kernel
theorem s197_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 3 = true := by decide +kernel
theorem s197_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 4 = true := by decide +kernel
theorem s197_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 5 = true := by decide +kernel
theorem k197_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k197_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k197_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k197_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k197_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k197_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k197_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s197_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k197_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k197_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k197_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k197_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k197_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k197_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 197) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (197 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k197_5_6_126 k h.1 (by omega)
theorem s197_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 5 7 = true := by decide +kernel
theorem s197_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 0 = true := by decide +kernel
theorem s197_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 1 = true := by decide +kernel
theorem s197_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 2 = true := by decide +kernel
theorem s197_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 3 = true := by decide +kernel
theorem s197_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 4 = true := by decide +kernel
theorem s197_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 5 = true := by decide +kernel
theorem s197_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 6 = true := by decide +kernel
theorem k197_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k197_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k197_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k197_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k197_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s197_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k197_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k197_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k197_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k197_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 197) ((InDA1.TCasaD 6 6 7).getD (197 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k197_6_7_12 k h.1 (by omega)
theorem col197_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 7 v) = true := by decide +kernel
theorem col197 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 197) 197 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col197_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col197_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col197_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s197_3_0
    · exact s197_3_1
    · exact s197_3_2
    · exact s197_3_3
    · exact s197_3_4
    · exact s197_3_5
    · exact s197_3_6
    · exact s197_3_7
  · fin_cases v
    · exact s197_4_0
    · exact s197_4_1
    · exact s197_4_2
    · exact s197_4_3
    · exact s197_4_4
    · exact s197_4_5
    · exact s197_4_6
    · exact s197_4_7
  · fin_cases v
    · exact s197_5_0
    · exact s197_5_1
    · exact s197_5_2
    · exact s197_5_3
    · exact s197_5_4
    · exact s197_5_5
    · exact s197_5_6
    · exact s197_5_7
  · fin_cases v
    · exact s197_6_0
    · exact s197_6_1
    · exact s197_6_2
    · exact s197_6_3
    · exact s197_6_4
    · exact s197_6_5
    · exact s197_6_6
    · exact s197_6_7
  · exact List.all_eq_true.mp col197_7 v (List.mem_finRange v)
theorem col198_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 0 v) = true := by decide +kernel
theorem col198_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 1 v) = true := by decide +kernel
theorem col198_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 2 v) = true := by decide +kernel
theorem s198_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 0 = true := by decide +kernel
theorem s198_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 1 = true := by decide +kernel
theorem s198_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 2 = true := by decide +kernel
theorem k198_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k198_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k198_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s198_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k198_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k198_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k198_3_3_26 k h.1 (by omega)
theorem s198_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 4 = true := by decide +kernel
theorem s198_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 5 = true := by decide +kernel
theorem k198_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k198_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k198_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k198_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k198_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k198_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k198_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k198_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k198_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k198_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k198_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s198_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k198_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k198_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k198_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k198_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k198_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k198_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k198_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k198_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k198_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k198_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k198_3_6_130 k h.1 (by omega)
theorem s198_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 3 7 = true := by decide +kernel
theorem s198_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 0 = true := by decide +kernel
theorem s198_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 1 = true := by decide +kernel
theorem s198_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 2 = true := by decide +kernel
theorem s198_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 3 = true := by decide +kernel
theorem s198_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 4 = true := by decide +kernel
theorem s198_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 5 = true := by decide +kernel
theorem k198_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k198_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k198_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k198_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k198_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k198_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k198_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s198_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k198_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k198_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k198_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k198_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k198_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k198_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k198_4_6_126 k h.1 (by omega)
theorem s198_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 4 7 = true := by decide +kernel
theorem s198_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 0 = true := by decide +kernel
theorem s198_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 1 = true := by decide +kernel
theorem s198_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 2 = true := by decide +kernel
theorem s198_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 3 = true := by decide +kernel
theorem s198_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 4 = true := by decide +kernel
theorem s198_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 5 = true := by decide +kernel
theorem k198_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k198_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k198_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k198_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k198_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k198_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k198_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s198_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k198_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k198_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k198_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k198_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k198_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k198_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 198) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (198 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k198_5_6_126 k h.1 (by omega)
theorem s198_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 5 7 = true := by decide +kernel
theorem s198_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 0 = true := by decide +kernel
theorem s198_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 1 = true := by decide +kernel
theorem s198_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 2 = true := by decide +kernel
theorem s198_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 3 = true := by decide +kernel
theorem s198_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 4 = true := by decide +kernel
theorem s198_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 5 = true := by decide +kernel
theorem s198_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 6 = true := by decide +kernel
theorem k198_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k198_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k198_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k198_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k198_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s198_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k198_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k198_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k198_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k198_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 198) ((InDA1.TCasaD 6 6 7).getD (198 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k198_6_7_12 k h.1 (by omega)
theorem col198_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 7 v) = true := by decide +kernel
theorem col198 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 198) 198 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col198_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col198_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col198_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s198_3_0
    · exact s198_3_1
    · exact s198_3_2
    · exact s198_3_3
    · exact s198_3_4
    · exact s198_3_5
    · exact s198_3_6
    · exact s198_3_7
  · fin_cases v
    · exact s198_4_0
    · exact s198_4_1
    · exact s198_4_2
    · exact s198_4_3
    · exact s198_4_4
    · exact s198_4_5
    · exact s198_4_6
    · exact s198_4_7
  · fin_cases v
    · exact s198_5_0
    · exact s198_5_1
    · exact s198_5_2
    · exact s198_5_3
    · exact s198_5_4
    · exact s198_5_5
    · exact s198_5_6
    · exact s198_5_7
  · fin_cases v
    · exact s198_6_0
    · exact s198_6_1
    · exact s198_6_2
    · exact s198_6_3
    · exact s198_6_4
    · exact s198_6_5
    · exact s198_6_6
    · exact s198_6_7
  · exact List.all_eq_true.mp col198_7 v (List.mem_finRange v)
theorem col199_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 0 v) = true := by decide +kernel
theorem col199_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 1 v) = true := by decide +kernel
theorem col199_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 2 v) = true := by decide +kernel
theorem s199_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 0 = true := by decide +kernel
theorem s199_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 1 = true := by decide +kernel
theorem s199_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 2 = true := by decide +kernel
theorem k199_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k199_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k199_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s199_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k199_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k199_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k199_3_3_26 k h.1 (by omega)
theorem s199_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 4 = true := by decide +kernel
theorem s199_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 5 = true := by decide +kernel
theorem k199_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k199_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k199_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k199_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k199_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k199_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k199_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k199_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k199_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k199_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k199_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s199_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k199_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k199_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k199_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k199_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k199_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k199_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k199_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k199_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k199_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k199_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k199_3_6_130 k h.1 (by omega)
theorem s199_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 3 7 = true := by decide +kernel
theorem s199_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 0 = true := by decide +kernel
theorem s199_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 1 = true := by decide +kernel
theorem s199_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 2 = true := by decide +kernel
theorem s199_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 3 = true := by decide +kernel
theorem s199_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 4 = true := by decide +kernel
theorem s199_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 5 = true := by decide +kernel
theorem k199_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k199_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k199_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k199_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k199_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k199_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k199_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s199_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k199_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k199_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k199_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k199_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k199_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k199_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k199_4_6_126 k h.1 (by omega)
theorem s199_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 4 7 = true := by decide +kernel
theorem s199_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 0 = true := by decide +kernel
theorem s199_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 1 = true := by decide +kernel
theorem s199_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 2 = true := by decide +kernel
theorem s199_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 3 = true := by decide +kernel
theorem s199_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 4 = true := by decide +kernel
theorem s199_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 5 = true := by decide +kernel
theorem k199_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k199_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k199_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k199_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k199_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k199_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k199_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s199_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k199_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k199_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k199_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k199_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k199_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k199_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 199) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (199 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k199_5_6_126 k h.1 (by omega)
theorem s199_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 5 7 = true := by decide +kernel
theorem s199_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 0 = true := by decide +kernel
theorem s199_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 1 = true := by decide +kernel
theorem s199_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 2 = true := by decide +kernel
theorem s199_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 3 = true := by decide +kernel
theorem s199_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 4 = true := by decide +kernel
theorem s199_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 5 = true := by decide +kernel
theorem s199_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 6 = true := by decide +kernel
theorem k199_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k199_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k199_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k199_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k199_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s199_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k199_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k199_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k199_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k199_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 199) ((InDA1.TCasaD 6 6 7).getD (199 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k199_6_7_12 k h.1 (by omega)
theorem col199_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 7 v) = true := by decide +kernel
theorem col199 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 199) 199 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col199_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col199_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col199_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s199_3_0
    · exact s199_3_1
    · exact s199_3_2
    · exact s199_3_3
    · exact s199_3_4
    · exact s199_3_5
    · exact s199_3_6
    · exact s199_3_7
  · fin_cases v
    · exact s199_4_0
    · exact s199_4_1
    · exact s199_4_2
    · exact s199_4_3
    · exact s199_4_4
    · exact s199_4_5
    · exact s199_4_6
    · exact s199_4_7
  · fin_cases v
    · exact s199_5_0
    · exact s199_5_1
    · exact s199_5_2
    · exact s199_5_3
    · exact s199_5_4
    · exact s199_5_5
    · exact s199_5_6
    · exact s199_5_7
  · fin_cases v
    · exact s199_6_0
    · exact s199_6_1
    · exact s199_6_2
    · exact s199_6_3
    · exact s199_6_4
    · exact s199_6_5
    · exact s199_6_6
    · exact s199_6_7
  · exact List.all_eq_true.mp col199_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
