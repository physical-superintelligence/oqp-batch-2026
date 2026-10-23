module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [170, 175). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col170_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 0 v) = true := by decide +kernel
theorem col170_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 1 v) = true := by decide +kernel
theorem col170_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 2 v) = true := by decide +kernel
theorem s170_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 0 = true := by decide +kernel
theorem s170_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 1 = true := by decide +kernel
theorem s170_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 2 = true := by decide +kernel
theorem k170_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k170_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k170_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s170_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k170_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k170_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k170_3_3_26 k h.1 (by omega)
theorem s170_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 4 = true := by decide +kernel
theorem s170_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 5 = true := by decide +kernel
theorem k170_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k170_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k170_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k170_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k170_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k170_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k170_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k170_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k170_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k170_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k170_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s170_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k170_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k170_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k170_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k170_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k170_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k170_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k170_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k170_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k170_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k170_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k170_3_6_130 k h.1 (by omega)
theorem s170_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 3 7 = true := by decide +kernel
theorem s170_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 0 = true := by decide +kernel
theorem s170_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 1 = true := by decide +kernel
theorem s170_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 2 = true := by decide +kernel
theorem s170_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 3 = true := by decide +kernel
theorem s170_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 4 = true := by decide +kernel
theorem s170_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 5 = true := by decide +kernel
theorem k170_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k170_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k170_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k170_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k170_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k170_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k170_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s170_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k170_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k170_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k170_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k170_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k170_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k170_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k170_4_6_126 k h.1 (by omega)
theorem s170_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 4 7 = true := by decide +kernel
theorem s170_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 0 = true := by decide +kernel
theorem s170_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 1 = true := by decide +kernel
theorem s170_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 2 = true := by decide +kernel
theorem s170_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 3 = true := by decide +kernel
theorem s170_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 4 = true := by decide +kernel
theorem s170_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 5 = true := by decide +kernel
theorem k170_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k170_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k170_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k170_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k170_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k170_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k170_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s170_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k170_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k170_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k170_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k170_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k170_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k170_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 170) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (170 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k170_5_6_126 k h.1 (by omega)
theorem s170_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 5 7 = true := by decide +kernel
theorem s170_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 0 = true := by decide +kernel
theorem s170_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 1 = true := by decide +kernel
theorem s170_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 2 = true := by decide +kernel
theorem s170_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 3 = true := by decide +kernel
theorem s170_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 4 = true := by decide +kernel
theorem s170_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 5 = true := by decide +kernel
theorem s170_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 6 = true := by decide +kernel
theorem k170_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k170_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k170_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k170_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k170_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s170_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k170_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k170_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k170_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k170_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 170) ((InDA1.TCasaD 6 6 7).getD (170 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k170_6_7_12 k h.1 (by omega)
theorem col170_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 7 v) = true := by decide +kernel
theorem col170 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 170) 170 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col170_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col170_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col170_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s170_3_0
    · exact s170_3_1
    · exact s170_3_2
    · exact s170_3_3
    · exact s170_3_4
    · exact s170_3_5
    · exact s170_3_6
    · exact s170_3_7
  · fin_cases v
    · exact s170_4_0
    · exact s170_4_1
    · exact s170_4_2
    · exact s170_4_3
    · exact s170_4_4
    · exact s170_4_5
    · exact s170_4_6
    · exact s170_4_7
  · fin_cases v
    · exact s170_5_0
    · exact s170_5_1
    · exact s170_5_2
    · exact s170_5_3
    · exact s170_5_4
    · exact s170_5_5
    · exact s170_5_6
    · exact s170_5_7
  · fin_cases v
    · exact s170_6_0
    · exact s170_6_1
    · exact s170_6_2
    · exact s170_6_3
    · exact s170_6_4
    · exact s170_6_5
    · exact s170_6_6
    · exact s170_6_7
  · exact List.all_eq_true.mp col170_7 v (List.mem_finRange v)
theorem col171_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 0 v) = true := by decide +kernel
theorem col171_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 1 v) = true := by decide +kernel
theorem col171_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 2 v) = true := by decide +kernel
theorem s171_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 0 = true := by decide +kernel
theorem s171_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 1 = true := by decide +kernel
theorem s171_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 2 = true := by decide +kernel
theorem k171_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k171_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k171_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s171_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k171_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k171_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k171_3_3_26 k h.1 (by omega)
theorem s171_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 4 = true := by decide +kernel
theorem s171_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 5 = true := by decide +kernel
theorem k171_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k171_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k171_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k171_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k171_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k171_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k171_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k171_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k171_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k171_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k171_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s171_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k171_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k171_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k171_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k171_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k171_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k171_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k171_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k171_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k171_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k171_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k171_3_6_130 k h.1 (by omega)
theorem s171_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 3 7 = true := by decide +kernel
theorem s171_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 0 = true := by decide +kernel
theorem s171_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 1 = true := by decide +kernel
theorem s171_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 2 = true := by decide +kernel
theorem s171_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 3 = true := by decide +kernel
theorem s171_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 4 = true := by decide +kernel
theorem s171_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 5 = true := by decide +kernel
theorem k171_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k171_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k171_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k171_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k171_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k171_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k171_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s171_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k171_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k171_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k171_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k171_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k171_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k171_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k171_4_6_126 k h.1 (by omega)
theorem s171_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 4 7 = true := by decide +kernel
theorem s171_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 0 = true := by decide +kernel
theorem s171_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 1 = true := by decide +kernel
theorem s171_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 2 = true := by decide +kernel
theorem s171_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 3 = true := by decide +kernel
theorem s171_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 4 = true := by decide +kernel
theorem s171_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 5 = true := by decide +kernel
theorem k171_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k171_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k171_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k171_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k171_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k171_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k171_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s171_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k171_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k171_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k171_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k171_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k171_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k171_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 171) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (171 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k171_5_6_126 k h.1 (by omega)
theorem s171_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 5 7 = true := by decide +kernel
theorem s171_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 0 = true := by decide +kernel
theorem s171_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 1 = true := by decide +kernel
theorem s171_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 2 = true := by decide +kernel
theorem s171_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 3 = true := by decide +kernel
theorem s171_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 4 = true := by decide +kernel
theorem s171_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 5 = true := by decide +kernel
theorem s171_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 6 = true := by decide +kernel
theorem k171_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k171_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k171_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k171_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k171_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s171_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k171_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k171_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k171_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k171_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 171) ((InDA1.TCasaD 6 6 7).getD (171 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k171_6_7_12 k h.1 (by omega)
theorem col171_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 7 v) = true := by decide +kernel
theorem col171 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 171) 171 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col171_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col171_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col171_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s171_3_0
    · exact s171_3_1
    · exact s171_3_2
    · exact s171_3_3
    · exact s171_3_4
    · exact s171_3_5
    · exact s171_3_6
    · exact s171_3_7
  · fin_cases v
    · exact s171_4_0
    · exact s171_4_1
    · exact s171_4_2
    · exact s171_4_3
    · exact s171_4_4
    · exact s171_4_5
    · exact s171_4_6
    · exact s171_4_7
  · fin_cases v
    · exact s171_5_0
    · exact s171_5_1
    · exact s171_5_2
    · exact s171_5_3
    · exact s171_5_4
    · exact s171_5_5
    · exact s171_5_6
    · exact s171_5_7
  · fin_cases v
    · exact s171_6_0
    · exact s171_6_1
    · exact s171_6_2
    · exact s171_6_3
    · exact s171_6_4
    · exact s171_6_5
    · exact s171_6_6
    · exact s171_6_7
  · exact List.all_eq_true.mp col171_7 v (List.mem_finRange v)
theorem col172_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 0 v) = true := by decide +kernel
theorem col172_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 1 v) = true := by decide +kernel
theorem col172_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 2 v) = true := by decide +kernel
theorem s172_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 0 = true := by decide +kernel
theorem s172_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 1 = true := by decide +kernel
theorem s172_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 2 = true := by decide +kernel
theorem k172_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k172_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k172_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s172_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k172_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k172_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k172_3_3_26 k h.1 (by omega)
theorem s172_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 4 = true := by decide +kernel
theorem s172_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 5 = true := by decide +kernel
theorem k172_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k172_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k172_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k172_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k172_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k172_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k172_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k172_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k172_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k172_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k172_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s172_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k172_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k172_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k172_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k172_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k172_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k172_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k172_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k172_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k172_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k172_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k172_3_6_130 k h.1 (by omega)
theorem s172_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 3 7 = true := by decide +kernel
theorem s172_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 0 = true := by decide +kernel
theorem s172_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 1 = true := by decide +kernel
theorem s172_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 2 = true := by decide +kernel
theorem s172_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 3 = true := by decide +kernel
theorem s172_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 4 = true := by decide +kernel
theorem s172_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 5 = true := by decide +kernel
theorem k172_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k172_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k172_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k172_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k172_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k172_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k172_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s172_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k172_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k172_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k172_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k172_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k172_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k172_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k172_4_6_126 k h.1 (by omega)
theorem s172_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 4 7 = true := by decide +kernel
theorem s172_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 0 = true := by decide +kernel
theorem s172_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 1 = true := by decide +kernel
theorem s172_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 2 = true := by decide +kernel
theorem s172_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 3 = true := by decide +kernel
theorem s172_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 4 = true := by decide +kernel
theorem s172_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 5 = true := by decide +kernel
theorem k172_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k172_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k172_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k172_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k172_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k172_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k172_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s172_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k172_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k172_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k172_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k172_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k172_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k172_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 172) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (172 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k172_5_6_126 k h.1 (by omega)
theorem s172_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 5 7 = true := by decide +kernel
theorem s172_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 0 = true := by decide +kernel
theorem s172_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 1 = true := by decide +kernel
theorem s172_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 2 = true := by decide +kernel
theorem s172_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 3 = true := by decide +kernel
theorem s172_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 4 = true := by decide +kernel
theorem s172_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 5 = true := by decide +kernel
theorem s172_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 6 = true := by decide +kernel
theorem k172_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k172_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k172_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k172_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k172_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s172_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k172_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k172_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k172_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k172_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 172) ((InDA1.TCasaD 6 6 7).getD (172 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k172_6_7_12 k h.1 (by omega)
theorem col172_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 7 v) = true := by decide +kernel
theorem col172 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 172) 172 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col172_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col172_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col172_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s172_3_0
    · exact s172_3_1
    · exact s172_3_2
    · exact s172_3_3
    · exact s172_3_4
    · exact s172_3_5
    · exact s172_3_6
    · exact s172_3_7
  · fin_cases v
    · exact s172_4_0
    · exact s172_4_1
    · exact s172_4_2
    · exact s172_4_3
    · exact s172_4_4
    · exact s172_4_5
    · exact s172_4_6
    · exact s172_4_7
  · fin_cases v
    · exact s172_5_0
    · exact s172_5_1
    · exact s172_5_2
    · exact s172_5_3
    · exact s172_5_4
    · exact s172_5_5
    · exact s172_5_6
    · exact s172_5_7
  · fin_cases v
    · exact s172_6_0
    · exact s172_6_1
    · exact s172_6_2
    · exact s172_6_3
    · exact s172_6_4
    · exact s172_6_5
    · exact s172_6_6
    · exact s172_6_7
  · exact List.all_eq_true.mp col172_7 v (List.mem_finRange v)
theorem col173_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 0 v) = true := by decide +kernel
theorem col173_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 1 v) = true := by decide +kernel
theorem col173_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 2 v) = true := by decide +kernel
theorem s173_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 0 = true := by decide +kernel
theorem s173_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 1 = true := by decide +kernel
theorem s173_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 2 = true := by decide +kernel
theorem k173_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k173_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k173_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s173_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k173_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k173_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k173_3_3_26 k h.1 (by omega)
theorem s173_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 4 = true := by decide +kernel
theorem s173_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 5 = true := by decide +kernel
theorem k173_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k173_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k173_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k173_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k173_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k173_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k173_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k173_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k173_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k173_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k173_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s173_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k173_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k173_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k173_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k173_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k173_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k173_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k173_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k173_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k173_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k173_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k173_3_6_130 k h.1 (by omega)
theorem s173_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 3 7 = true := by decide +kernel
theorem s173_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 0 = true := by decide +kernel
theorem s173_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 1 = true := by decide +kernel
theorem s173_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 2 = true := by decide +kernel
theorem s173_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 3 = true := by decide +kernel
theorem s173_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 4 = true := by decide +kernel
theorem s173_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 5 = true := by decide +kernel
theorem k173_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k173_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k173_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k173_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k173_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k173_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k173_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s173_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k173_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k173_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k173_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k173_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k173_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k173_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k173_4_6_126 k h.1 (by omega)
theorem s173_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 4 7 = true := by decide +kernel
theorem s173_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 0 = true := by decide +kernel
theorem s173_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 1 = true := by decide +kernel
theorem s173_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 2 = true := by decide +kernel
theorem s173_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 3 = true := by decide +kernel
theorem s173_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 4 = true := by decide +kernel
theorem s173_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 5 = true := by decide +kernel
theorem k173_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k173_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k173_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k173_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k173_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k173_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k173_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s173_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k173_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k173_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k173_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k173_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k173_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k173_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 173) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (173 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k173_5_6_126 k h.1 (by omega)
theorem s173_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 5 7 = true := by decide +kernel
theorem s173_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 0 = true := by decide +kernel
theorem s173_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 1 = true := by decide +kernel
theorem s173_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 2 = true := by decide +kernel
theorem s173_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 3 = true := by decide +kernel
theorem s173_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 4 = true := by decide +kernel
theorem s173_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 5 = true := by decide +kernel
theorem s173_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 6 = true := by decide +kernel
theorem k173_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k173_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k173_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k173_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k173_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s173_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k173_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k173_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k173_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k173_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 173) ((InDA1.TCasaD 6 6 7).getD (173 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k173_6_7_12 k h.1 (by omega)
theorem col173_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 7 v) = true := by decide +kernel
theorem col173 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 173) 173 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col173_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col173_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col173_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s173_3_0
    · exact s173_3_1
    · exact s173_3_2
    · exact s173_3_3
    · exact s173_3_4
    · exact s173_3_5
    · exact s173_3_6
    · exact s173_3_7
  · fin_cases v
    · exact s173_4_0
    · exact s173_4_1
    · exact s173_4_2
    · exact s173_4_3
    · exact s173_4_4
    · exact s173_4_5
    · exact s173_4_6
    · exact s173_4_7
  · fin_cases v
    · exact s173_5_0
    · exact s173_5_1
    · exact s173_5_2
    · exact s173_5_3
    · exact s173_5_4
    · exact s173_5_5
    · exact s173_5_6
    · exact s173_5_7
  · fin_cases v
    · exact s173_6_0
    · exact s173_6_1
    · exact s173_6_2
    · exact s173_6_3
    · exact s173_6_4
    · exact s173_6_5
    · exact s173_6_6
    · exact s173_6_7
  · exact List.all_eq_true.mp col173_7 v (List.mem_finRange v)
theorem col174_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 0 v) = true := by decide +kernel
theorem col174_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 1 v) = true := by decide +kernel
theorem col174_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 2 v) = true := by decide +kernel
theorem s174_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 0 = true := by decide +kernel
theorem s174_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 1 = true := by decide +kernel
theorem s174_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 2 = true := by decide +kernel
theorem k174_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k174_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k174_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s174_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k174_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k174_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k174_3_3_26 k h.1 (by omega)
theorem s174_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 4 = true := by decide +kernel
theorem s174_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 5 = true := by decide +kernel
theorem k174_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k174_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k174_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k174_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k174_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k174_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k174_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k174_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k174_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k174_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k174_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s174_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k174_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k174_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k174_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k174_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k174_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k174_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k174_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k174_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k174_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k174_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k174_3_6_130 k h.1 (by omega)
theorem s174_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 3 7 = true := by decide +kernel
theorem s174_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 0 = true := by decide +kernel
theorem s174_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 1 = true := by decide +kernel
theorem s174_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 2 = true := by decide +kernel
theorem s174_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 3 = true := by decide +kernel
theorem s174_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 4 = true := by decide +kernel
theorem s174_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 5 = true := by decide +kernel
theorem k174_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k174_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k174_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k174_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k174_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k174_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k174_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s174_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k174_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k174_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k174_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k174_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k174_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k174_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k174_4_6_126 k h.1 (by omega)
theorem s174_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 4 7 = true := by decide +kernel
theorem s174_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 0 = true := by decide +kernel
theorem s174_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 1 = true := by decide +kernel
theorem s174_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 2 = true := by decide +kernel
theorem s174_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 3 = true := by decide +kernel
theorem s174_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 4 = true := by decide +kernel
theorem s174_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 5 = true := by decide +kernel
theorem k174_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k174_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k174_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k174_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k174_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k174_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k174_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s174_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k174_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k174_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k174_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k174_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k174_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k174_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 174) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (174 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k174_5_6_126 k h.1 (by omega)
theorem s174_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 5 7 = true := by decide +kernel
theorem s174_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 0 = true := by decide +kernel
theorem s174_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 1 = true := by decide +kernel
theorem s174_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 2 = true := by decide +kernel
theorem s174_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 3 = true := by decide +kernel
theorem s174_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 4 = true := by decide +kernel
theorem s174_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 5 = true := by decide +kernel
theorem s174_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 6 = true := by decide +kernel
theorem k174_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k174_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k174_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k174_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k174_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s174_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k174_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k174_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k174_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k174_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 174) ((InDA1.TCasaD 6 6 7).getD (174 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k174_6_7_12 k h.1 (by omega)
theorem col174_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 7 v) = true := by decide +kernel
theorem col174 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 174) 174 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col174_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col174_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col174_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s174_3_0
    · exact s174_3_1
    · exact s174_3_2
    · exact s174_3_3
    · exact s174_3_4
    · exact s174_3_5
    · exact s174_3_6
    · exact s174_3_7
  · fin_cases v
    · exact s174_4_0
    · exact s174_4_1
    · exact s174_4_2
    · exact s174_4_3
    · exact s174_4_4
    · exact s174_4_5
    · exact s174_4_6
    · exact s174_4_7
  · fin_cases v
    · exact s174_5_0
    · exact s174_5_1
    · exact s174_5_2
    · exact s174_5_3
    · exact s174_5_4
    · exact s174_5_5
    · exact s174_5_6
    · exact s174_5_7
  · fin_cases v
    · exact s174_6_0
    · exact s174_6_1
    · exact s174_6_2
    · exact s174_6_3
    · exact s174_6_4
    · exact s174_6_5
    · exact s174_6_6
    · exact s174_6_7
  · exact List.all_eq_true.mp col174_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
