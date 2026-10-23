module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [220, 225). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col220_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 0 v) = true := by decide +kernel
theorem col220_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 1 v) = true := by decide +kernel
theorem col220_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 2 v) = true := by decide +kernel
theorem s220_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 0 = true := by decide +kernel
theorem s220_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 1 = true := by decide +kernel
theorem s220_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 2 = true := by decide +kernel
theorem k220_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k220_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k220_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s220_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k220_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k220_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k220_3_3_26 k h.1 (by omega)
theorem s220_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 4 = true := by decide +kernel
theorem s220_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 5 = true := by decide +kernel
theorem k220_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k220_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k220_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k220_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k220_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k220_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k220_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k220_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k220_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k220_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k220_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s220_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k220_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k220_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k220_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k220_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k220_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k220_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k220_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k220_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k220_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k220_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k220_3_6_130 k h.1 (by omega)
theorem s220_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 3 7 = true := by decide +kernel
theorem s220_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 0 = true := by decide +kernel
theorem s220_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 1 = true := by decide +kernel
theorem s220_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 2 = true := by decide +kernel
theorem s220_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 3 = true := by decide +kernel
theorem s220_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 4 = true := by decide +kernel
theorem s220_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 5 = true := by decide +kernel
theorem k220_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k220_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k220_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k220_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k220_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k220_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k220_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s220_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k220_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k220_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k220_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k220_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k220_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k220_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k220_4_6_126 k h.1 (by omega)
theorem s220_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 4 7 = true := by decide +kernel
theorem s220_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 0 = true := by decide +kernel
theorem s220_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 1 = true := by decide +kernel
theorem s220_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 2 = true := by decide +kernel
theorem s220_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 3 = true := by decide +kernel
theorem s220_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 4 = true := by decide +kernel
theorem s220_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 5 = true := by decide +kernel
theorem k220_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k220_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k220_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k220_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k220_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k220_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k220_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s220_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k220_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k220_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k220_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k220_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k220_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k220_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k220_5_6_126 k h.1 (by omega)
theorem s220_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 5 7 = true := by decide +kernel
theorem s220_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 0 = true := by decide +kernel
theorem s220_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 1 = true := by decide +kernel
theorem s220_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 2 = true := by decide +kernel
theorem k220_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k220_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k220_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k220_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k220_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k220_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k220_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k220_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k220_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k220_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k220_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k220_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s220_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k220_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k220_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k220_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k220_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k220_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k220_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k220_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k220_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k220_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k220_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k220_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k220_6_3_33 k h.1 (by omega)
theorem k220_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k220_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k220_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k220_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k220_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k220_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k220_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s220_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k220_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k220_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k220_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k220_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k220_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k220_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k220_6_4_18 k h.1 (by omega)
theorem k220_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k220_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k220_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k220_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k220_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k220_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k220_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s220_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k220_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k220_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k220_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k220_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k220_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k220_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k220_6_5_18 k h.1 (by omega)
theorem k220_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k220_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k220_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k220_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k220_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k220_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k220_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k220_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k220_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k220_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k220_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k220_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k220_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k220_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k220_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k220_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k220_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k220_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k220_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k220_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k220_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k220_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k220_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k220_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k220_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k220_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k220_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k220_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k220_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k220_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k220_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k220_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k220_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k220_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k220_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k220_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k220_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k220_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k220_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k220_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k220_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k220_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k220_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k220_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k220_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k220_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s220_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k220_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k220_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k220_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k220_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k220_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k220_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k220_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k220_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k220_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k220_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k220_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k220_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k220_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k220_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k220_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k220_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k220_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k220_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k220_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k220_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k220_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k220_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k220_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k220_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k220_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k220_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k220_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k220_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k220_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k220_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k220_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k220_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k220_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k220_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k220_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k220_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k220_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k220_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k220_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k220_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k220_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k220_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k220_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k220_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k220_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k220_6_6_135 k h.1 (by omega)
theorem k220_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k220_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k220_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k220_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k220_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s220_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k220_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k220_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k220_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k220_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 220) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (220 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k220_6_7_12 k h.1 (by omega)
theorem col220_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 7 v) = true := by decide +kernel
theorem col220 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 220) 220 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col220_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col220_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col220_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s220_3_0
    · exact s220_3_1
    · exact s220_3_2
    · exact s220_3_3
    · exact s220_3_4
    · exact s220_3_5
    · exact s220_3_6
    · exact s220_3_7
  · fin_cases v
    · exact s220_4_0
    · exact s220_4_1
    · exact s220_4_2
    · exact s220_4_3
    · exact s220_4_4
    · exact s220_4_5
    · exact s220_4_6
    · exact s220_4_7
  · fin_cases v
    · exact s220_5_0
    · exact s220_5_1
    · exact s220_5_2
    · exact s220_5_3
    · exact s220_5_4
    · exact s220_5_5
    · exact s220_5_6
    · exact s220_5_7
  · fin_cases v
    · exact s220_6_0
    · exact s220_6_1
    · exact s220_6_2
    · exact s220_6_3
    · exact s220_6_4
    · exact s220_6_5
    · exact s220_6_6
    · exact s220_6_7
  · exact List.all_eq_true.mp col220_7 v (List.mem_finRange v)
theorem col221_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 0 v) = true := by decide +kernel
theorem col221_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 1 v) = true := by decide +kernel
theorem col221_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 2 v) = true := by decide +kernel
theorem s221_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 0 = true := by decide +kernel
theorem s221_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 1 = true := by decide +kernel
theorem s221_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 2 = true := by decide +kernel
theorem k221_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k221_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k221_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s221_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k221_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k221_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k221_3_3_26 k h.1 (by omega)
theorem s221_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 4 = true := by decide +kernel
theorem s221_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 5 = true := by decide +kernel
theorem k221_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k221_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k221_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k221_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k221_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k221_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k221_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k221_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k221_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k221_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k221_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s221_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k221_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k221_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k221_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k221_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k221_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k221_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k221_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k221_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k221_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k221_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k221_3_6_130 k h.1 (by omega)
theorem s221_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 3 7 = true := by decide +kernel
theorem s221_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 0 = true := by decide +kernel
theorem s221_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 1 = true := by decide +kernel
theorem s221_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 2 = true := by decide +kernel
theorem s221_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 3 = true := by decide +kernel
theorem s221_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 4 = true := by decide +kernel
theorem s221_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 5 = true := by decide +kernel
theorem k221_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k221_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k221_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k221_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k221_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k221_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k221_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s221_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k221_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k221_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k221_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k221_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k221_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k221_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k221_4_6_126 k h.1 (by omega)
theorem s221_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 4 7 = true := by decide +kernel
theorem s221_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 0 = true := by decide +kernel
theorem s221_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 1 = true := by decide +kernel
theorem s221_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 2 = true := by decide +kernel
theorem s221_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 3 = true := by decide +kernel
theorem s221_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 4 = true := by decide +kernel
theorem s221_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 5 = true := by decide +kernel
theorem k221_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k221_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k221_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k221_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k221_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k221_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k221_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s221_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k221_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k221_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k221_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k221_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k221_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k221_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k221_5_6_126 k h.1 (by omega)
theorem s221_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 5 7 = true := by decide +kernel
theorem s221_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 0 = true := by decide +kernel
theorem s221_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 1 = true := by decide +kernel
theorem s221_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 2 = true := by decide +kernel
theorem k221_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k221_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k221_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k221_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k221_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k221_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k221_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k221_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k221_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k221_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k221_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k221_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s221_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k221_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k221_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k221_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k221_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k221_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k221_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k221_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k221_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k221_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k221_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k221_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k221_6_3_33 k h.1 (by omega)
theorem k221_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k221_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k221_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k221_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k221_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k221_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k221_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s221_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k221_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k221_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k221_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k221_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k221_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k221_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k221_6_4_18 k h.1 (by omega)
theorem k221_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k221_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k221_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k221_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k221_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k221_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k221_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s221_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k221_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k221_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k221_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k221_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k221_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k221_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k221_6_5_18 k h.1 (by omega)
theorem k221_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k221_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k221_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k221_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k221_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k221_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k221_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k221_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k221_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k221_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k221_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k221_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k221_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k221_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k221_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k221_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k221_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k221_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k221_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k221_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k221_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k221_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k221_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k221_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k221_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k221_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k221_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k221_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k221_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k221_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k221_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k221_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k221_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k221_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k221_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k221_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k221_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k221_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k221_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k221_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k221_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k221_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k221_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k221_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k221_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k221_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s221_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k221_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k221_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k221_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k221_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k221_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k221_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k221_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k221_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k221_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k221_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k221_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k221_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k221_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k221_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k221_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k221_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k221_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k221_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k221_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k221_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k221_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k221_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k221_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k221_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k221_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k221_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k221_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k221_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k221_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k221_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k221_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k221_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k221_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k221_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k221_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k221_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k221_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k221_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k221_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k221_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k221_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k221_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k221_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k221_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k221_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k221_6_6_135 k h.1 (by omega)
theorem k221_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k221_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k221_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k221_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k221_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s221_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k221_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k221_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k221_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k221_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 221) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (221 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k221_6_7_12 k h.1 (by omega)
theorem col221_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 7 v) = true := by decide +kernel
theorem col221 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 221) 221 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col221_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col221_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col221_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s221_3_0
    · exact s221_3_1
    · exact s221_3_2
    · exact s221_3_3
    · exact s221_3_4
    · exact s221_3_5
    · exact s221_3_6
    · exact s221_3_7
  · fin_cases v
    · exact s221_4_0
    · exact s221_4_1
    · exact s221_4_2
    · exact s221_4_3
    · exact s221_4_4
    · exact s221_4_5
    · exact s221_4_6
    · exact s221_4_7
  · fin_cases v
    · exact s221_5_0
    · exact s221_5_1
    · exact s221_5_2
    · exact s221_5_3
    · exact s221_5_4
    · exact s221_5_5
    · exact s221_5_6
    · exact s221_5_7
  · fin_cases v
    · exact s221_6_0
    · exact s221_6_1
    · exact s221_6_2
    · exact s221_6_3
    · exact s221_6_4
    · exact s221_6_5
    · exact s221_6_6
    · exact s221_6_7
  · exact List.all_eq_true.mp col221_7 v (List.mem_finRange v)
theorem col222_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 0 v) = true := by decide +kernel
theorem col222_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 1 v) = true := by decide +kernel
theorem col222_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 2 v) = true := by decide +kernel
theorem s222_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 0 = true := by decide +kernel
theorem s222_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 1 = true := by decide +kernel
theorem s222_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 2 = true := by decide +kernel
theorem k222_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k222_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k222_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s222_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k222_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k222_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k222_3_3_26 k h.1 (by omega)
theorem s222_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 4 = true := by decide +kernel
theorem s222_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 5 = true := by decide +kernel
theorem k222_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k222_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k222_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k222_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k222_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k222_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k222_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k222_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k222_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k222_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k222_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s222_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k222_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k222_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k222_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k222_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k222_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k222_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k222_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k222_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k222_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k222_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k222_3_6_130 k h.1 (by omega)
theorem s222_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 3 7 = true := by decide +kernel
theorem s222_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 0 = true := by decide +kernel
theorem s222_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 1 = true := by decide +kernel
theorem s222_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 2 = true := by decide +kernel
theorem s222_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 3 = true := by decide +kernel
theorem s222_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 4 = true := by decide +kernel
theorem s222_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 5 = true := by decide +kernel
theorem k222_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k222_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k222_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k222_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k222_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k222_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k222_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s222_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k222_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k222_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k222_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k222_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k222_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k222_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k222_4_6_126 k h.1 (by omega)
theorem s222_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 4 7 = true := by decide +kernel
theorem s222_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 0 = true := by decide +kernel
theorem s222_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 1 = true := by decide +kernel
theorem s222_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 2 = true := by decide +kernel
theorem s222_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 3 = true := by decide +kernel
theorem s222_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 4 = true := by decide +kernel
theorem s222_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 5 = true := by decide +kernel
theorem k222_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k222_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k222_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k222_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k222_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k222_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k222_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s222_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k222_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k222_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k222_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k222_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k222_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k222_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k222_5_6_126 k h.1 (by omega)
theorem s222_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 5 7 = true := by decide +kernel
theorem s222_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 0 = true := by decide +kernel
theorem s222_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 1 = true := by decide +kernel
theorem s222_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 2 = true := by decide +kernel
theorem k222_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k222_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k222_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k222_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k222_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k222_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k222_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k222_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k222_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k222_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k222_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k222_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s222_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k222_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k222_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k222_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k222_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k222_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k222_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k222_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k222_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k222_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k222_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k222_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k222_6_3_33 k h.1 (by omega)
theorem k222_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k222_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k222_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k222_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k222_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k222_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k222_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s222_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k222_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k222_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k222_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k222_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k222_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k222_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k222_6_4_18 k h.1 (by omega)
theorem k222_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k222_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k222_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k222_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k222_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k222_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k222_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s222_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k222_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k222_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k222_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k222_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k222_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k222_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k222_6_5_18 k h.1 (by omega)
theorem k222_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k222_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k222_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k222_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k222_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k222_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k222_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k222_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k222_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k222_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k222_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k222_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k222_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k222_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k222_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k222_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k222_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k222_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k222_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k222_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k222_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k222_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k222_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k222_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k222_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k222_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k222_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k222_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k222_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k222_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k222_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k222_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k222_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k222_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k222_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k222_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k222_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k222_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k222_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k222_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k222_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k222_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k222_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k222_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k222_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k222_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s222_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k222_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k222_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k222_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k222_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k222_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k222_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k222_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k222_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k222_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k222_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k222_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k222_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k222_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k222_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k222_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k222_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k222_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k222_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k222_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k222_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k222_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k222_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k222_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k222_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k222_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k222_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k222_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k222_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k222_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k222_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k222_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k222_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k222_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k222_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k222_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k222_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k222_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k222_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k222_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k222_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k222_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k222_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k222_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k222_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k222_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k222_6_6_135 k h.1 (by omega)
theorem k222_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k222_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k222_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k222_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k222_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s222_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k222_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k222_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k222_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k222_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 222) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (222 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k222_6_7_12 k h.1 (by omega)
theorem col222_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 7 v) = true := by decide +kernel
theorem col222 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 222) 222 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col222_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col222_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col222_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s222_3_0
    · exact s222_3_1
    · exact s222_3_2
    · exact s222_3_3
    · exact s222_3_4
    · exact s222_3_5
    · exact s222_3_6
    · exact s222_3_7
  · fin_cases v
    · exact s222_4_0
    · exact s222_4_1
    · exact s222_4_2
    · exact s222_4_3
    · exact s222_4_4
    · exact s222_4_5
    · exact s222_4_6
    · exact s222_4_7
  · fin_cases v
    · exact s222_5_0
    · exact s222_5_1
    · exact s222_5_2
    · exact s222_5_3
    · exact s222_5_4
    · exact s222_5_5
    · exact s222_5_6
    · exact s222_5_7
  · fin_cases v
    · exact s222_6_0
    · exact s222_6_1
    · exact s222_6_2
    · exact s222_6_3
    · exact s222_6_4
    · exact s222_6_5
    · exact s222_6_6
    · exact s222_6_7
  · exact List.all_eq_true.mp col222_7 v (List.mem_finRange v)
theorem col223_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 0 v) = true := by decide +kernel
theorem col223_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 1 v) = true := by decide +kernel
theorem col223_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 2 v) = true := by decide +kernel
theorem s223_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 0 = true := by decide +kernel
theorem s223_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 1 = true := by decide +kernel
theorem s223_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 2 = true := by decide +kernel
theorem k223_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k223_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k223_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s223_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k223_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k223_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k223_3_3_26 k h.1 (by omega)
theorem s223_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 4 = true := by decide +kernel
theorem s223_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 5 = true := by decide +kernel
theorem k223_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k223_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k223_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k223_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k223_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k223_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k223_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k223_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k223_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k223_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k223_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s223_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k223_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k223_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k223_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k223_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k223_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k223_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k223_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k223_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k223_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k223_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k223_3_6_130 k h.1 (by omega)
theorem s223_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 3 7 = true := by decide +kernel
theorem s223_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 0 = true := by decide +kernel
theorem s223_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 1 = true := by decide +kernel
theorem s223_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 2 = true := by decide +kernel
theorem s223_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 3 = true := by decide +kernel
theorem s223_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 4 = true := by decide +kernel
theorem s223_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 5 = true := by decide +kernel
theorem k223_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k223_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k223_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k223_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k223_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k223_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k223_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s223_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k223_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k223_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k223_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k223_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k223_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k223_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k223_4_6_126 k h.1 (by omega)
theorem s223_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 4 7 = true := by decide +kernel
theorem s223_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 0 = true := by decide +kernel
theorem s223_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 1 = true := by decide +kernel
theorem s223_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 2 = true := by decide +kernel
theorem s223_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 3 = true := by decide +kernel
theorem s223_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 4 = true := by decide +kernel
theorem s223_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 5 = true := by decide +kernel
theorem k223_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k223_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k223_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k223_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k223_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k223_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k223_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s223_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k223_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k223_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k223_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k223_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k223_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k223_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k223_5_6_126 k h.1 (by omega)
theorem s223_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 5 7 = true := by decide +kernel
theorem s223_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 0 = true := by decide +kernel
theorem s223_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 1 = true := by decide +kernel
theorem s223_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 2 = true := by decide +kernel
theorem k223_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k223_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k223_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k223_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k223_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k223_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k223_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k223_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k223_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k223_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k223_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k223_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s223_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k223_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k223_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k223_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k223_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k223_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k223_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k223_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k223_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k223_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k223_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k223_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k223_6_3_33 k h.1 (by omega)
theorem k223_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k223_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k223_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k223_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k223_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k223_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k223_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s223_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k223_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k223_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k223_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k223_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k223_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k223_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k223_6_4_18 k h.1 (by omega)
theorem k223_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k223_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k223_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k223_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k223_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k223_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k223_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s223_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k223_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k223_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k223_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k223_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k223_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k223_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k223_6_5_18 k h.1 (by omega)
theorem k223_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k223_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k223_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k223_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k223_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k223_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k223_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k223_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k223_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k223_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k223_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k223_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k223_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k223_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k223_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k223_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k223_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k223_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k223_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k223_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k223_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k223_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k223_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k223_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k223_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k223_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k223_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k223_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k223_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k223_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k223_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k223_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k223_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k223_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k223_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k223_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k223_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k223_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k223_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k223_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k223_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k223_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k223_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k223_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k223_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k223_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s223_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k223_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k223_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k223_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k223_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k223_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k223_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k223_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k223_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k223_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k223_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k223_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k223_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k223_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k223_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k223_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k223_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k223_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k223_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k223_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k223_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k223_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k223_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k223_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k223_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k223_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k223_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k223_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k223_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k223_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k223_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k223_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k223_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k223_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k223_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k223_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k223_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k223_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k223_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k223_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k223_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k223_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k223_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k223_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k223_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k223_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k223_6_6_135 k h.1 (by omega)
theorem k223_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k223_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k223_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k223_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k223_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s223_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k223_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k223_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k223_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k223_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 223) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (223 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k223_6_7_12 k h.1 (by omega)
theorem col223_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 7 v) = true := by decide +kernel
theorem col223 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 223) 223 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col223_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col223_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col223_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s223_3_0
    · exact s223_3_1
    · exact s223_3_2
    · exact s223_3_3
    · exact s223_3_4
    · exact s223_3_5
    · exact s223_3_6
    · exact s223_3_7
  · fin_cases v
    · exact s223_4_0
    · exact s223_4_1
    · exact s223_4_2
    · exact s223_4_3
    · exact s223_4_4
    · exact s223_4_5
    · exact s223_4_6
    · exact s223_4_7
  · fin_cases v
    · exact s223_5_0
    · exact s223_5_1
    · exact s223_5_2
    · exact s223_5_3
    · exact s223_5_4
    · exact s223_5_5
    · exact s223_5_6
    · exact s223_5_7
  · fin_cases v
    · exact s223_6_0
    · exact s223_6_1
    · exact s223_6_2
    · exact s223_6_3
    · exact s223_6_4
    · exact s223_6_5
    · exact s223_6_6
    · exact s223_6_7
  · exact List.all_eq_true.mp col223_7 v (List.mem_finRange v)
theorem col224_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 0 v) = true := by decide +kernel
theorem col224_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 1 v) = true := by decide +kernel
theorem col224_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 2 v) = true := by decide +kernel
theorem s224_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 0 = true := by decide +kernel
theorem s224_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 1 = true := by decide +kernel
theorem s224_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 2 = true := by decide +kernel
theorem k224_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k224_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k224_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s224_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k224_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k224_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k224_3_3_26 k h.1 (by omega)
theorem s224_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 4 = true := by decide +kernel
theorem s224_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 5 = true := by decide +kernel
theorem k224_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k224_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k224_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k224_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k224_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k224_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k224_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k224_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k224_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k224_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k224_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s224_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k224_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k224_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k224_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k224_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k224_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k224_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k224_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k224_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k224_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k224_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k224_3_6_130 k h.1 (by omega)
theorem s224_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 3 7 = true := by decide +kernel
theorem s224_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 0 = true := by decide +kernel
theorem s224_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 1 = true := by decide +kernel
theorem s224_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 2 = true := by decide +kernel
theorem s224_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 3 = true := by decide +kernel
theorem s224_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 4 = true := by decide +kernel
theorem s224_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 5 = true := by decide +kernel
theorem k224_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k224_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k224_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k224_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k224_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k224_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k224_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s224_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k224_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k224_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k224_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k224_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k224_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k224_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k224_4_6_126 k h.1 (by omega)
theorem s224_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 4 7 = true := by decide +kernel
theorem s224_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 0 = true := by decide +kernel
theorem s224_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 1 = true := by decide +kernel
theorem s224_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 2 = true := by decide +kernel
theorem s224_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 3 = true := by decide +kernel
theorem s224_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 4 = true := by decide +kernel
theorem s224_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 5 = true := by decide +kernel
theorem k224_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k224_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k224_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k224_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k224_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k224_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k224_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s224_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k224_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k224_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k224_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k224_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k224_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k224_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k224_5_6_126 k h.1 (by omega)
theorem s224_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 5 7 = true := by decide +kernel
theorem s224_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 0 = true := by decide +kernel
theorem s224_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 1 = true := by decide +kernel
theorem s224_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 2 = true := by decide +kernel
theorem k224_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k224_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k224_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k224_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k224_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k224_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k224_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k224_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k224_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k224_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k224_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k224_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s224_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k224_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k224_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k224_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k224_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k224_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k224_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k224_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k224_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k224_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k224_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k224_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k224_6_3_33 k h.1 (by omega)
theorem k224_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k224_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k224_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k224_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k224_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k224_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k224_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s224_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k224_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k224_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k224_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k224_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k224_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k224_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k224_6_4_18 k h.1 (by omega)
theorem k224_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k224_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k224_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k224_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k224_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k224_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k224_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s224_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k224_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k224_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k224_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k224_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k224_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k224_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k224_6_5_18 k h.1 (by omega)
theorem k224_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k224_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k224_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k224_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k224_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k224_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k224_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k224_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k224_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k224_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k224_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k224_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k224_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k224_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k224_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k224_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k224_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k224_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k224_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k224_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k224_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k224_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k224_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k224_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k224_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k224_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k224_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k224_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k224_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k224_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k224_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k224_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k224_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k224_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k224_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k224_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k224_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k224_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k224_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k224_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k224_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k224_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k224_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k224_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k224_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k224_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s224_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k224_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k224_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k224_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k224_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k224_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k224_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k224_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k224_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k224_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k224_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k224_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k224_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k224_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k224_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k224_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k224_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k224_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k224_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k224_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k224_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k224_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k224_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k224_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k224_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k224_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k224_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k224_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k224_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k224_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k224_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k224_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k224_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k224_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k224_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k224_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k224_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k224_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k224_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k224_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k224_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k224_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k224_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k224_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k224_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k224_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k224_6_6_135 k h.1 (by omega)
theorem k224_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k224_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k224_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k224_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k224_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s224_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k224_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k224_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k224_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k224_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 224) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (224 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k224_6_7_12 k h.1 (by omega)
theorem col224_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 7 v) = true := by decide +kernel
theorem col224 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 224) 224 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col224_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col224_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col224_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s224_3_0
    · exact s224_3_1
    · exact s224_3_2
    · exact s224_3_3
    · exact s224_3_4
    · exact s224_3_5
    · exact s224_3_6
    · exact s224_3_7
  · fin_cases v
    · exact s224_4_0
    · exact s224_4_1
    · exact s224_4_2
    · exact s224_4_3
    · exact s224_4_4
    · exact s224_4_5
    · exact s224_4_6
    · exact s224_4_7
  · fin_cases v
    · exact s224_5_0
    · exact s224_5_1
    · exact s224_5_2
    · exact s224_5_3
    · exact s224_5_4
    · exact s224_5_5
    · exact s224_5_6
    · exact s224_5_7
  · fin_cases v
    · exact s224_6_0
    · exact s224_6_1
    · exact s224_6_2
    · exact s224_6_3
    · exact s224_6_4
    · exact s224_6_5
    · exact s224_6_6
    · exact s224_6_7
  · exact List.all_eq_true.mp col224_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
