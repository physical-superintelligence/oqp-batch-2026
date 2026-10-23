module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [130, 135). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col130_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 0 v) = true := by decide +kernel
theorem col130_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 1 v) = true := by decide +kernel
theorem col130_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 2 v) = true := by decide +kernel
theorem s130_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 0 = true := by decide +kernel
theorem s130_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 1 = true := by decide +kernel
theorem s130_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 2 = true := by decide +kernel
theorem k130_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k130_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k130_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s130_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k130_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k130_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k130_3_3_26 k h.1 (by omega)
theorem s130_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 4 = true := by decide +kernel
theorem s130_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 5 = true := by decide +kernel
theorem k130_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k130_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k130_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k130_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k130_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k130_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k130_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k130_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k130_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k130_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k130_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s130_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k130_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k130_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k130_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k130_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k130_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k130_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k130_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k130_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k130_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k130_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k130_3_6_130 k h.1 (by omega)
theorem s130_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 3 7 = true := by decide +kernel
theorem s130_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 0 = true := by decide +kernel
theorem s130_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 1 = true := by decide +kernel
theorem s130_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 2 = true := by decide +kernel
theorem s130_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 3 = true := by decide +kernel
theorem s130_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 4 = true := by decide +kernel
theorem s130_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 5 = true := by decide +kernel
theorem k130_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k130_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k130_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k130_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k130_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k130_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k130_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s130_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k130_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k130_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k130_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k130_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k130_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k130_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k130_4_6_126 k h.1 (by omega)
theorem s130_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 4 7 = true := by decide +kernel
theorem s130_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 0 = true := by decide +kernel
theorem s130_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 1 = true := by decide +kernel
theorem s130_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 2 = true := by decide +kernel
theorem s130_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 3 = true := by decide +kernel
theorem s130_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 4 = true := by decide +kernel
theorem s130_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 5 = true := by decide +kernel
theorem k130_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k130_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k130_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k130_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k130_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k130_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k130_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s130_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k130_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k130_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k130_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k130_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k130_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k130_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 130) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (130 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k130_5_6_126 k h.1 (by omega)
theorem s130_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 5 7 = true := by decide +kernel
theorem s130_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 0 = true := by decide +kernel
theorem s130_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 1 = true := by decide +kernel
theorem s130_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 2 = true := by decide +kernel
theorem s130_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 3 = true := by decide +kernel
theorem s130_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 4 = true := by decide +kernel
theorem s130_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 5 = true := by decide +kernel
theorem s130_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 6 = true := by decide +kernel
theorem k130_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k130_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k130_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k130_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k130_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s130_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k130_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k130_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k130_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k130_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 130) ((InDA1.TCasaD 6 6 7).getD (130 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k130_6_7_12 k h.1 (by omega)
theorem col130_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 7 v) = true := by decide +kernel
theorem col130 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 130) 130 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col130_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col130_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col130_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s130_6_0
    · exact s130_6_1
    · exact s130_6_2
    · exact s130_6_3
    · exact s130_6_4
    · exact s130_6_5
    · exact s130_6_6
    · exact s130_6_7
  · exact List.all_eq_true.mp col130_7 v (List.mem_finRange v)
theorem col131_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 0 v) = true := by decide +kernel
theorem col131_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 1 v) = true := by decide +kernel
theorem col131_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 2 v) = true := by decide +kernel
theorem s131_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 0 = true := by decide +kernel
theorem s131_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 1 = true := by decide +kernel
theorem s131_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 2 = true := by decide +kernel
theorem k131_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k131_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k131_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s131_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k131_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k131_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k131_3_3_26 k h.1 (by omega)
theorem s131_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 4 = true := by decide +kernel
theorem s131_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 5 = true := by decide +kernel
theorem k131_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k131_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k131_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k131_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k131_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k131_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k131_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k131_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k131_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k131_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k131_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s131_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k131_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k131_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k131_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k131_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k131_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k131_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k131_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k131_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k131_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k131_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k131_3_6_130 k h.1 (by omega)
theorem s131_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 3 7 = true := by decide +kernel
theorem s131_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 0 = true := by decide +kernel
theorem s131_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 1 = true := by decide +kernel
theorem s131_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 2 = true := by decide +kernel
theorem s131_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 3 = true := by decide +kernel
theorem s131_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 4 = true := by decide +kernel
theorem s131_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 5 = true := by decide +kernel
theorem k131_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k131_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k131_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k131_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k131_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k131_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k131_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s131_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k131_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k131_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k131_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k131_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k131_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k131_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k131_4_6_126 k h.1 (by omega)
theorem s131_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 4 7 = true := by decide +kernel
theorem s131_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 0 = true := by decide +kernel
theorem s131_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 1 = true := by decide +kernel
theorem s131_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 2 = true := by decide +kernel
theorem s131_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 3 = true := by decide +kernel
theorem s131_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 4 = true := by decide +kernel
theorem s131_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 5 = true := by decide +kernel
theorem k131_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k131_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k131_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k131_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k131_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k131_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k131_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s131_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k131_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k131_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k131_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k131_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k131_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k131_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 131) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (131 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k131_5_6_126 k h.1 (by omega)
theorem s131_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 5 7 = true := by decide +kernel
theorem s131_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 0 = true := by decide +kernel
theorem s131_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 1 = true := by decide +kernel
theorem s131_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 2 = true := by decide +kernel
theorem s131_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 3 = true := by decide +kernel
theorem s131_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 4 = true := by decide +kernel
theorem s131_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 5 = true := by decide +kernel
theorem s131_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 6 = true := by decide +kernel
theorem k131_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k131_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k131_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k131_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k131_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s131_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k131_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k131_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k131_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k131_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 131) ((InDA1.TCasaD 6 6 7).getD (131 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k131_6_7_12 k h.1 (by omega)
theorem col131_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 7 v) = true := by decide +kernel
theorem col131 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 131) 131 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col131_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col131_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col131_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s131_6_0
    · exact s131_6_1
    · exact s131_6_2
    · exact s131_6_3
    · exact s131_6_4
    · exact s131_6_5
    · exact s131_6_6
    · exact s131_6_7
  · exact List.all_eq_true.mp col131_7 v (List.mem_finRange v)
theorem col132_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 0 v) = true := by decide +kernel
theorem col132_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 1 v) = true := by decide +kernel
theorem col132_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 2 v) = true := by decide +kernel
theorem s132_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 0 = true := by decide +kernel
theorem s132_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 1 = true := by decide +kernel
theorem s132_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 2 = true := by decide +kernel
theorem k132_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k132_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k132_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s132_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k132_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k132_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k132_3_3_26 k h.1 (by omega)
theorem s132_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 4 = true := by decide +kernel
theorem s132_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 5 = true := by decide +kernel
theorem k132_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k132_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k132_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k132_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k132_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k132_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k132_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k132_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k132_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k132_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k132_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s132_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k132_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k132_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k132_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k132_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k132_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k132_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k132_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k132_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k132_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k132_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k132_3_6_130 k h.1 (by omega)
theorem s132_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 3 7 = true := by decide +kernel
theorem s132_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 0 = true := by decide +kernel
theorem s132_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 1 = true := by decide +kernel
theorem s132_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 2 = true := by decide +kernel
theorem s132_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 3 = true := by decide +kernel
theorem s132_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 4 = true := by decide +kernel
theorem s132_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 5 = true := by decide +kernel
theorem k132_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k132_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k132_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k132_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k132_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k132_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k132_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s132_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k132_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k132_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k132_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k132_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k132_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k132_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k132_4_6_126 k h.1 (by omega)
theorem s132_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 4 7 = true := by decide +kernel
theorem s132_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 0 = true := by decide +kernel
theorem s132_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 1 = true := by decide +kernel
theorem s132_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 2 = true := by decide +kernel
theorem s132_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 3 = true := by decide +kernel
theorem s132_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 4 = true := by decide +kernel
theorem s132_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 5 = true := by decide +kernel
theorem k132_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k132_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k132_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k132_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k132_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k132_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k132_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s132_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k132_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k132_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k132_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k132_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k132_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k132_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 132) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (132 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k132_5_6_126 k h.1 (by omega)
theorem s132_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 5 7 = true := by decide +kernel
theorem s132_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 0 = true := by decide +kernel
theorem s132_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 1 = true := by decide +kernel
theorem s132_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 2 = true := by decide +kernel
theorem s132_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 3 = true := by decide +kernel
theorem s132_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 4 = true := by decide +kernel
theorem s132_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 5 = true := by decide +kernel
theorem s132_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 6 = true := by decide +kernel
theorem k132_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k132_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k132_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k132_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k132_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s132_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k132_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k132_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k132_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k132_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 132) ((InDA1.TCasaD 6 6 7).getD (132 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k132_6_7_12 k h.1 (by omega)
theorem col132_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 7 v) = true := by decide +kernel
theorem col132 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 132) 132 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col132_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col132_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col132_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s132_6_0
    · exact s132_6_1
    · exact s132_6_2
    · exact s132_6_3
    · exact s132_6_4
    · exact s132_6_5
    · exact s132_6_6
    · exact s132_6_7
  · exact List.all_eq_true.mp col132_7 v (List.mem_finRange v)
theorem col133_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 0 v) = true := by decide +kernel
theorem col133_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 1 v) = true := by decide +kernel
theorem col133_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 2 v) = true := by decide +kernel
theorem s133_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 0 = true := by decide +kernel
theorem s133_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 1 = true := by decide +kernel
theorem s133_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 2 = true := by decide +kernel
theorem k133_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k133_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k133_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s133_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k133_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k133_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k133_3_3_26 k h.1 (by omega)
theorem s133_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 4 = true := by decide +kernel
theorem s133_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 5 = true := by decide +kernel
theorem k133_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k133_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k133_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k133_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k133_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k133_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k133_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k133_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k133_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k133_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k133_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s133_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k133_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k133_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k133_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k133_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k133_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k133_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k133_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k133_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k133_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k133_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k133_3_6_130 k h.1 (by omega)
theorem s133_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 3 7 = true := by decide +kernel
theorem s133_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 0 = true := by decide +kernel
theorem s133_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 1 = true := by decide +kernel
theorem s133_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 2 = true := by decide +kernel
theorem s133_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 3 = true := by decide +kernel
theorem s133_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 4 = true := by decide +kernel
theorem s133_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 5 = true := by decide +kernel
theorem k133_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k133_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k133_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k133_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k133_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k133_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k133_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s133_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k133_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k133_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k133_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k133_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k133_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k133_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k133_4_6_126 k h.1 (by omega)
theorem s133_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 4 7 = true := by decide +kernel
theorem s133_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 0 = true := by decide +kernel
theorem s133_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 1 = true := by decide +kernel
theorem s133_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 2 = true := by decide +kernel
theorem s133_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 3 = true := by decide +kernel
theorem s133_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 4 = true := by decide +kernel
theorem s133_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 5 = true := by decide +kernel
theorem k133_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k133_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k133_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k133_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k133_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k133_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k133_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s133_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k133_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k133_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k133_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k133_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k133_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k133_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 133) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (133 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k133_5_6_126 k h.1 (by omega)
theorem s133_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 5 7 = true := by decide +kernel
theorem s133_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 0 = true := by decide +kernel
theorem s133_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 1 = true := by decide +kernel
theorem s133_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 2 = true := by decide +kernel
theorem s133_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 3 = true := by decide +kernel
theorem s133_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 4 = true := by decide +kernel
theorem s133_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 5 = true := by decide +kernel
theorem s133_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 6 = true := by decide +kernel
theorem k133_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k133_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k133_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k133_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k133_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s133_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k133_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k133_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k133_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k133_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 133) ((InDA1.TCasaD 6 6 7).getD (133 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k133_6_7_12 k h.1 (by omega)
theorem col133_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 7 v) = true := by decide +kernel
theorem col133 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 133) 133 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col133_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col133_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col133_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s133_6_0
    · exact s133_6_1
    · exact s133_6_2
    · exact s133_6_3
    · exact s133_6_4
    · exact s133_6_5
    · exact s133_6_6
    · exact s133_6_7
  · exact List.all_eq_true.mp col133_7 v (List.mem_finRange v)
theorem col134_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 0 v) = true := by decide +kernel
theorem col134_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 1 v) = true := by decide +kernel
theorem col134_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 2 v) = true := by decide +kernel
theorem s134_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 0 = true := by decide +kernel
theorem s134_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 1 = true := by decide +kernel
theorem s134_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 2 = true := by decide +kernel
theorem k134_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k134_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k134_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s134_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k134_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k134_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k134_3_3_26 k h.1 (by omega)
theorem s134_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 4 = true := by decide +kernel
theorem s134_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 5 = true := by decide +kernel
theorem k134_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k134_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k134_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k134_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k134_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k134_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k134_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k134_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k134_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k134_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k134_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s134_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k134_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k134_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k134_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k134_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k134_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k134_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k134_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k134_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k134_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k134_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k134_3_6_130 k h.1 (by omega)
theorem s134_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 3 7 = true := by decide +kernel
theorem s134_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 0 = true := by decide +kernel
theorem s134_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 1 = true := by decide +kernel
theorem s134_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 2 = true := by decide +kernel
theorem s134_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 3 = true := by decide +kernel
theorem s134_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 4 = true := by decide +kernel
theorem s134_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 5 = true := by decide +kernel
theorem k134_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k134_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k134_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k134_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k134_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k134_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k134_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s134_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k134_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k134_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k134_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k134_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k134_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k134_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k134_4_6_126 k h.1 (by omega)
theorem s134_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 4 7 = true := by decide +kernel
theorem s134_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 0 = true := by decide +kernel
theorem s134_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 1 = true := by decide +kernel
theorem s134_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 2 = true := by decide +kernel
theorem s134_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 3 = true := by decide +kernel
theorem s134_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 4 = true := by decide +kernel
theorem s134_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 5 = true := by decide +kernel
theorem k134_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k134_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k134_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k134_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k134_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k134_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k134_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s134_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k134_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k134_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k134_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k134_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k134_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k134_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 134) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (134 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k134_5_6_126 k h.1 (by omega)
theorem s134_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 5 7 = true := by decide +kernel
theorem s134_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 0 = true := by decide +kernel
theorem s134_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 1 = true := by decide +kernel
theorem s134_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 2 = true := by decide +kernel
theorem s134_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 3 = true := by decide +kernel
theorem s134_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 4 = true := by decide +kernel
theorem s134_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 5 = true := by decide +kernel
theorem s134_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 6 = true := by decide +kernel
theorem k134_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k134_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k134_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k134_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k134_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s134_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k134_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k134_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k134_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k134_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 134) ((InDA1.TCasaD 6 6 7).getD (134 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k134_6_7_12 k h.1 (by omega)
theorem col134_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 7 v) = true := by decide +kernel
theorem col134 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 134) 134 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col134_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col134_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col134_2 v (List.mem_finRange v)
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
  · fin_cases v
    · exact s134_6_0
    · exact s134_6_1
    · exact s134_6_2
    · exact s134_6_3
    · exact s134_6_4
    · exact s134_6_5
    · exact s134_6_6
    · exact s134_6_7
  · exact List.all_eq_true.mp col134_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
