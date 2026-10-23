module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [135, 140). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col135_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 0 v) = true := by decide +kernel
theorem col135_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 1 v) = true := by decide +kernel
theorem col135_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 2 v) = true := by decide +kernel
theorem s135_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 0 = true := by decide +kernel
theorem s135_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 1 = true := by decide +kernel
theorem s135_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 2 = true := by decide +kernel
theorem k135_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k135_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k135_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s135_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k135_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k135_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k135_3_3_26 k h.1 (by omega)
theorem s135_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 4 = true := by decide +kernel
theorem s135_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 5 = true := by decide +kernel
theorem k135_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k135_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k135_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k135_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k135_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k135_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k135_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k135_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k135_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k135_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k135_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s135_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k135_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k135_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k135_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k135_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k135_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k135_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k135_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k135_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k135_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k135_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k135_3_6_130 k h.1 (by omega)
theorem s135_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 3 7 = true := by decide +kernel
theorem s135_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 0 = true := by decide +kernel
theorem s135_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 1 = true := by decide +kernel
theorem s135_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 2 = true := by decide +kernel
theorem s135_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 3 = true := by decide +kernel
theorem s135_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 4 = true := by decide +kernel
theorem s135_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 5 = true := by decide +kernel
theorem k135_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k135_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k135_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k135_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k135_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k135_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k135_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s135_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k135_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k135_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k135_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k135_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k135_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k135_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k135_4_6_126 k h.1 (by omega)
theorem s135_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 4 7 = true := by decide +kernel
theorem s135_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 0 = true := by decide +kernel
theorem s135_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 1 = true := by decide +kernel
theorem s135_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 2 = true := by decide +kernel
theorem s135_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 3 = true := by decide +kernel
theorem s135_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 4 = true := by decide +kernel
theorem s135_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 5 = true := by decide +kernel
theorem k135_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k135_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k135_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k135_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k135_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k135_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k135_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s135_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k135_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k135_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k135_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k135_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k135_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k135_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 135) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (135 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k135_5_6_126 k h.1 (by omega)
theorem s135_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 5 7 = true := by decide +kernel
theorem s135_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 0 = true := by decide +kernel
theorem s135_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 1 = true := by decide +kernel
theorem s135_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 2 = true := by decide +kernel
theorem s135_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 3 = true := by decide +kernel
theorem s135_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 4 = true := by decide +kernel
theorem s135_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 5 = true := by decide +kernel
theorem s135_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 6 = true := by decide +kernel
theorem k135_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k135_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k135_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k135_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k135_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s135_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k135_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k135_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k135_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k135_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 135) ((InDA1.TCasaD 6 6 7).getD (135 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k135_6_7_12 k h.1 (by omega)
theorem col135_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 7 v) = true := by decide +kernel
theorem col135 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 135) 135 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col135_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col135_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col135_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s135_3_0
    · exact s135_3_1
    · exact s135_3_2
    · exact s135_3_3
    · exact s135_3_4
    · exact s135_3_5
    · exact s135_3_6
    · exact s135_3_7
  · fin_cases v
    · exact s135_4_0
    · exact s135_4_1
    · exact s135_4_2
    · exact s135_4_3
    · exact s135_4_4
    · exact s135_4_5
    · exact s135_4_6
    · exact s135_4_7
  · fin_cases v
    · exact s135_5_0
    · exact s135_5_1
    · exact s135_5_2
    · exact s135_5_3
    · exact s135_5_4
    · exact s135_5_5
    · exact s135_5_6
    · exact s135_5_7
  · fin_cases v
    · exact s135_6_0
    · exact s135_6_1
    · exact s135_6_2
    · exact s135_6_3
    · exact s135_6_4
    · exact s135_6_5
    · exact s135_6_6
    · exact s135_6_7
  · exact List.all_eq_true.mp col135_7 v (List.mem_finRange v)
theorem col136_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 0 v) = true := by decide +kernel
theorem col136_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 1 v) = true := by decide +kernel
theorem col136_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 2 v) = true := by decide +kernel
theorem s136_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 0 = true := by decide +kernel
theorem s136_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 1 = true := by decide +kernel
theorem s136_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 2 = true := by decide +kernel
theorem k136_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k136_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k136_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s136_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k136_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k136_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k136_3_3_26 k h.1 (by omega)
theorem s136_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 4 = true := by decide +kernel
theorem s136_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 5 = true := by decide +kernel
theorem k136_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k136_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k136_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k136_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k136_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k136_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k136_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k136_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k136_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k136_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k136_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s136_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k136_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k136_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k136_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k136_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k136_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k136_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k136_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k136_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k136_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k136_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k136_3_6_130 k h.1 (by omega)
theorem s136_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 3 7 = true := by decide +kernel
theorem s136_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 0 = true := by decide +kernel
theorem s136_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 1 = true := by decide +kernel
theorem s136_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 2 = true := by decide +kernel
theorem s136_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 3 = true := by decide +kernel
theorem s136_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 4 = true := by decide +kernel
theorem s136_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 5 = true := by decide +kernel
theorem k136_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k136_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k136_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k136_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k136_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k136_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k136_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s136_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k136_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k136_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k136_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k136_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k136_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k136_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k136_4_6_126 k h.1 (by omega)
theorem s136_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 4 7 = true := by decide +kernel
theorem s136_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 0 = true := by decide +kernel
theorem s136_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 1 = true := by decide +kernel
theorem s136_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 2 = true := by decide +kernel
theorem s136_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 3 = true := by decide +kernel
theorem s136_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 4 = true := by decide +kernel
theorem s136_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 5 = true := by decide +kernel
theorem k136_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k136_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k136_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k136_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k136_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k136_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k136_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s136_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k136_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k136_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k136_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k136_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k136_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k136_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 136) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (136 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k136_5_6_126 k h.1 (by omega)
theorem s136_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 5 7 = true := by decide +kernel
theorem s136_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 0 = true := by decide +kernel
theorem s136_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 1 = true := by decide +kernel
theorem s136_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 2 = true := by decide +kernel
theorem s136_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 3 = true := by decide +kernel
theorem s136_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 4 = true := by decide +kernel
theorem s136_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 5 = true := by decide +kernel
theorem s136_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 6 = true := by decide +kernel
theorem k136_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k136_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k136_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k136_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k136_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s136_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k136_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k136_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k136_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k136_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 136) ((InDA1.TCasaD 6 6 7).getD (136 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k136_6_7_12 k h.1 (by omega)
theorem col136_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 7 v) = true := by decide +kernel
theorem col136 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 136) 136 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col136_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col136_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col136_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s136_3_0
    · exact s136_3_1
    · exact s136_3_2
    · exact s136_3_3
    · exact s136_3_4
    · exact s136_3_5
    · exact s136_3_6
    · exact s136_3_7
  · fin_cases v
    · exact s136_4_0
    · exact s136_4_1
    · exact s136_4_2
    · exact s136_4_3
    · exact s136_4_4
    · exact s136_4_5
    · exact s136_4_6
    · exact s136_4_7
  · fin_cases v
    · exact s136_5_0
    · exact s136_5_1
    · exact s136_5_2
    · exact s136_5_3
    · exact s136_5_4
    · exact s136_5_5
    · exact s136_5_6
    · exact s136_5_7
  · fin_cases v
    · exact s136_6_0
    · exact s136_6_1
    · exact s136_6_2
    · exact s136_6_3
    · exact s136_6_4
    · exact s136_6_5
    · exact s136_6_6
    · exact s136_6_7
  · exact List.all_eq_true.mp col136_7 v (List.mem_finRange v)
theorem col137_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 0 v) = true := by decide +kernel
theorem col137_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 1 v) = true := by decide +kernel
theorem col137_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 2 v) = true := by decide +kernel
theorem s137_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 0 = true := by decide +kernel
theorem s137_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 1 = true := by decide +kernel
theorem s137_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 2 = true := by decide +kernel
theorem k137_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k137_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k137_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s137_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k137_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k137_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k137_3_3_26 k h.1 (by omega)
theorem s137_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 4 = true := by decide +kernel
theorem s137_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 5 = true := by decide +kernel
theorem k137_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k137_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k137_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k137_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k137_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k137_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k137_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k137_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k137_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k137_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k137_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s137_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k137_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k137_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k137_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k137_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k137_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k137_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k137_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k137_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k137_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k137_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k137_3_6_130 k h.1 (by omega)
theorem s137_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 3 7 = true := by decide +kernel
theorem s137_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 0 = true := by decide +kernel
theorem s137_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 1 = true := by decide +kernel
theorem s137_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 2 = true := by decide +kernel
theorem s137_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 3 = true := by decide +kernel
theorem s137_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 4 = true := by decide +kernel
theorem s137_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 5 = true := by decide +kernel
theorem k137_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k137_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k137_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k137_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k137_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k137_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k137_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s137_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k137_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k137_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k137_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k137_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k137_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k137_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k137_4_6_126 k h.1 (by omega)
theorem s137_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 4 7 = true := by decide +kernel
theorem s137_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 0 = true := by decide +kernel
theorem s137_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 1 = true := by decide +kernel
theorem s137_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 2 = true := by decide +kernel
theorem s137_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 3 = true := by decide +kernel
theorem s137_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 4 = true := by decide +kernel
theorem s137_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 5 = true := by decide +kernel
theorem k137_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k137_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k137_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k137_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k137_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k137_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k137_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s137_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k137_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k137_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k137_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k137_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k137_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k137_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 137) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (137 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k137_5_6_126 k h.1 (by omega)
theorem s137_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 5 7 = true := by decide +kernel
theorem s137_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 0 = true := by decide +kernel
theorem s137_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 1 = true := by decide +kernel
theorem s137_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 2 = true := by decide +kernel
theorem s137_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 3 = true := by decide +kernel
theorem s137_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 4 = true := by decide +kernel
theorem s137_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 5 = true := by decide +kernel
theorem s137_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 6 = true := by decide +kernel
theorem k137_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k137_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k137_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k137_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k137_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s137_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k137_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k137_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k137_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k137_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 137) ((InDA1.TCasaD 6 6 7).getD (137 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k137_6_7_12 k h.1 (by omega)
theorem col137_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 7 v) = true := by decide +kernel
theorem col137 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 137) 137 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col137_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col137_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col137_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s137_3_0
    · exact s137_3_1
    · exact s137_3_2
    · exact s137_3_3
    · exact s137_3_4
    · exact s137_3_5
    · exact s137_3_6
    · exact s137_3_7
  · fin_cases v
    · exact s137_4_0
    · exact s137_4_1
    · exact s137_4_2
    · exact s137_4_3
    · exact s137_4_4
    · exact s137_4_5
    · exact s137_4_6
    · exact s137_4_7
  · fin_cases v
    · exact s137_5_0
    · exact s137_5_1
    · exact s137_5_2
    · exact s137_5_3
    · exact s137_5_4
    · exact s137_5_5
    · exact s137_5_6
    · exact s137_5_7
  · fin_cases v
    · exact s137_6_0
    · exact s137_6_1
    · exact s137_6_2
    · exact s137_6_3
    · exact s137_6_4
    · exact s137_6_5
    · exact s137_6_6
    · exact s137_6_7
  · exact List.all_eq_true.mp col137_7 v (List.mem_finRange v)
theorem col138_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 0 v) = true := by decide +kernel
theorem col138_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 1 v) = true := by decide +kernel
theorem col138_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 2 v) = true := by decide +kernel
theorem s138_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 0 = true := by decide +kernel
theorem s138_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 1 = true := by decide +kernel
theorem s138_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 2 = true := by decide +kernel
theorem k138_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k138_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k138_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s138_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k138_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k138_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k138_3_3_26 k h.1 (by omega)
theorem s138_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 4 = true := by decide +kernel
theorem s138_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 5 = true := by decide +kernel
theorem k138_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k138_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k138_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k138_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k138_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k138_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k138_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k138_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k138_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k138_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k138_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s138_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k138_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k138_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k138_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k138_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k138_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k138_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k138_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k138_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k138_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k138_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k138_3_6_130 k h.1 (by omega)
theorem s138_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 3 7 = true := by decide +kernel
theorem s138_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 0 = true := by decide +kernel
theorem s138_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 1 = true := by decide +kernel
theorem s138_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 2 = true := by decide +kernel
theorem s138_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 3 = true := by decide +kernel
theorem s138_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 4 = true := by decide +kernel
theorem s138_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 5 = true := by decide +kernel
theorem k138_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k138_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k138_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k138_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k138_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k138_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k138_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s138_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k138_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k138_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k138_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k138_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k138_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k138_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k138_4_6_126 k h.1 (by omega)
theorem s138_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 4 7 = true := by decide +kernel
theorem s138_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 0 = true := by decide +kernel
theorem s138_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 1 = true := by decide +kernel
theorem s138_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 2 = true := by decide +kernel
theorem s138_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 3 = true := by decide +kernel
theorem s138_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 4 = true := by decide +kernel
theorem s138_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 5 = true := by decide +kernel
theorem k138_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k138_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k138_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k138_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k138_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k138_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k138_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s138_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k138_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k138_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k138_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k138_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k138_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k138_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 138) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (138 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k138_5_6_126 k h.1 (by omega)
theorem s138_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 5 7 = true := by decide +kernel
theorem s138_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 0 = true := by decide +kernel
theorem s138_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 1 = true := by decide +kernel
theorem s138_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 2 = true := by decide +kernel
theorem s138_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 3 = true := by decide +kernel
theorem s138_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 4 = true := by decide +kernel
theorem s138_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 5 = true := by decide +kernel
theorem s138_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 6 = true := by decide +kernel
theorem k138_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k138_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k138_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k138_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k138_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s138_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k138_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k138_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k138_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k138_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 138) ((InDA1.TCasaD 6 6 7).getD (138 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k138_6_7_12 k h.1 (by omega)
theorem col138_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 7 v) = true := by decide +kernel
theorem col138 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 138) 138 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col138_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col138_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col138_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s138_3_0
    · exact s138_3_1
    · exact s138_3_2
    · exact s138_3_3
    · exact s138_3_4
    · exact s138_3_5
    · exact s138_3_6
    · exact s138_3_7
  · fin_cases v
    · exact s138_4_0
    · exact s138_4_1
    · exact s138_4_2
    · exact s138_4_3
    · exact s138_4_4
    · exact s138_4_5
    · exact s138_4_6
    · exact s138_4_7
  · fin_cases v
    · exact s138_5_0
    · exact s138_5_1
    · exact s138_5_2
    · exact s138_5_3
    · exact s138_5_4
    · exact s138_5_5
    · exact s138_5_6
    · exact s138_5_7
  · fin_cases v
    · exact s138_6_0
    · exact s138_6_1
    · exact s138_6_2
    · exact s138_6_3
    · exact s138_6_4
    · exact s138_6_5
    · exact s138_6_6
    · exact s138_6_7
  · exact List.all_eq_true.mp col138_7 v (List.mem_finRange v)
theorem col139_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 0 v) = true := by decide +kernel
theorem col139_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 1 v) = true := by decide +kernel
theorem col139_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 2 v) = true := by decide +kernel
theorem s139_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 0 = true := by decide +kernel
theorem s139_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 1 = true := by decide +kernel
theorem s139_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 2 = true := by decide +kernel
theorem k139_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k139_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k139_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s139_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k139_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k139_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k139_3_3_26 k h.1 (by omega)
theorem s139_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 4 = true := by decide +kernel
theorem s139_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 5 = true := by decide +kernel
theorem k139_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k139_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k139_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k139_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k139_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k139_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k139_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k139_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k139_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k139_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k139_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s139_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k139_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k139_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k139_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k139_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k139_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k139_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k139_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k139_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k139_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k139_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k139_3_6_130 k h.1 (by omega)
theorem s139_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 3 7 = true := by decide +kernel
theorem s139_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 0 = true := by decide +kernel
theorem s139_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 1 = true := by decide +kernel
theorem s139_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 2 = true := by decide +kernel
theorem s139_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 3 = true := by decide +kernel
theorem s139_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 4 = true := by decide +kernel
theorem s139_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 5 = true := by decide +kernel
theorem k139_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k139_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k139_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k139_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k139_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k139_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k139_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s139_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k139_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k139_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k139_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k139_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k139_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k139_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k139_4_6_126 k h.1 (by omega)
theorem s139_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 4 7 = true := by decide +kernel
theorem s139_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 0 = true := by decide +kernel
theorem s139_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 1 = true := by decide +kernel
theorem s139_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 2 = true := by decide +kernel
theorem s139_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 3 = true := by decide +kernel
theorem s139_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 4 = true := by decide +kernel
theorem s139_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 5 = true := by decide +kernel
theorem k139_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k139_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k139_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k139_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k139_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k139_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k139_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s139_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k139_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k139_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k139_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k139_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k139_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k139_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 139) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (139 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k139_5_6_126 k h.1 (by omega)
theorem s139_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 5 7 = true := by decide +kernel
theorem s139_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 0 = true := by decide +kernel
theorem s139_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 1 = true := by decide +kernel
theorem s139_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 2 = true := by decide +kernel
theorem s139_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 3 = true := by decide +kernel
theorem s139_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 4 = true := by decide +kernel
theorem s139_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 5 = true := by decide +kernel
theorem s139_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 6 = true := by decide +kernel
theorem k139_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k139_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k139_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k139_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k139_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s139_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k139_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k139_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k139_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k139_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 139) ((InDA1.TCasaD 6 6 7).getD (139 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k139_6_7_12 k h.1 (by omega)
theorem col139_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 7 v) = true := by decide +kernel
theorem col139 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 139) 139 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col139_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col139_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col139_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s139_3_0
    · exact s139_3_1
    · exact s139_3_2
    · exact s139_3_3
    · exact s139_3_4
    · exact s139_3_5
    · exact s139_3_6
    · exact s139_3_7
  · fin_cases v
    · exact s139_4_0
    · exact s139_4_1
    · exact s139_4_2
    · exact s139_4_3
    · exact s139_4_4
    · exact s139_4_5
    · exact s139_4_6
    · exact s139_4_7
  · fin_cases v
    · exact s139_5_0
    · exact s139_5_1
    · exact s139_5_2
    · exact s139_5_3
    · exact s139_5_4
    · exact s139_5_5
    · exact s139_5_6
    · exact s139_5_7
  · fin_cases v
    · exact s139_6_0
    · exact s139_6_1
    · exact s139_6_2
    · exact s139_6_3
    · exact s139_6_4
    · exact s139_6_5
    · exact s139_6_6
    · exact s139_6_7
  · exact List.all_eq_true.mp col139_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
