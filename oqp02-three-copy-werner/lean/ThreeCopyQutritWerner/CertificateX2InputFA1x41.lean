module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [205, 210). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col205_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 0 v) = true := by decide +kernel
theorem col205_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 1 v) = true := by decide +kernel
theorem col205_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 2 v) = true := by decide +kernel
theorem s205_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 0 = true := by decide +kernel
theorem s205_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 1 = true := by decide +kernel
theorem s205_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 2 = true := by decide +kernel
theorem k205_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k205_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k205_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s205_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k205_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k205_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k205_3_3_26 k h.1 (by omega)
theorem s205_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 4 = true := by decide +kernel
theorem s205_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 5 = true := by decide +kernel
theorem k205_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k205_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k205_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k205_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k205_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k205_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k205_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k205_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k205_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k205_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k205_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s205_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k205_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k205_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k205_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k205_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k205_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k205_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k205_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k205_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k205_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k205_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k205_3_6_130 k h.1 (by omega)
theorem s205_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 3 7 = true := by decide +kernel
theorem s205_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 0 = true := by decide +kernel
theorem s205_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 1 = true := by decide +kernel
theorem s205_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 2 = true := by decide +kernel
theorem s205_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 3 = true := by decide +kernel
theorem s205_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 4 = true := by decide +kernel
theorem s205_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 5 = true := by decide +kernel
theorem k205_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k205_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k205_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k205_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k205_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k205_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k205_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s205_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k205_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k205_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k205_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k205_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k205_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k205_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k205_4_6_126 k h.1 (by omega)
theorem s205_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 4 7 = true := by decide +kernel
theorem s205_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 0 = true := by decide +kernel
theorem s205_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 1 = true := by decide +kernel
theorem s205_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 2 = true := by decide +kernel
theorem s205_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 3 = true := by decide +kernel
theorem s205_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 4 = true := by decide +kernel
theorem s205_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 5 = true := by decide +kernel
theorem k205_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k205_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k205_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k205_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k205_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k205_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k205_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s205_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k205_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k205_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k205_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k205_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k205_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k205_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 205) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (205 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k205_5_6_126 k h.1 (by omega)
theorem s205_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 5 7 = true := by decide +kernel
theorem s205_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 0 = true := by decide +kernel
theorem s205_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 1 = true := by decide +kernel
theorem s205_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 2 = true := by decide +kernel
theorem s205_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 3 = true := by decide +kernel
theorem s205_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 4 = true := by decide +kernel
theorem s205_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 5 = true := by decide +kernel
theorem s205_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 6 = true := by decide +kernel
theorem k205_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k205_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k205_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k205_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k205_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s205_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k205_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k205_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k205_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k205_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 205) ((InDA1.TCasaD 6 6 7).getD (205 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k205_6_7_12 k h.1 (by omega)
theorem col205_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 7 v) = true := by decide +kernel
theorem col205 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 205) 205 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col205_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col205_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col205_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s205_3_0
    · exact s205_3_1
    · exact s205_3_2
    · exact s205_3_3
    · exact s205_3_4
    · exact s205_3_5
    · exact s205_3_6
    · exact s205_3_7
  · fin_cases v
    · exact s205_4_0
    · exact s205_4_1
    · exact s205_4_2
    · exact s205_4_3
    · exact s205_4_4
    · exact s205_4_5
    · exact s205_4_6
    · exact s205_4_7
  · fin_cases v
    · exact s205_5_0
    · exact s205_5_1
    · exact s205_5_2
    · exact s205_5_3
    · exact s205_5_4
    · exact s205_5_5
    · exact s205_5_6
    · exact s205_5_7
  · fin_cases v
    · exact s205_6_0
    · exact s205_6_1
    · exact s205_6_2
    · exact s205_6_3
    · exact s205_6_4
    · exact s205_6_5
    · exact s205_6_6
    · exact s205_6_7
  · exact List.all_eq_true.mp col205_7 v (List.mem_finRange v)
theorem col206_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 0 v) = true := by decide +kernel
theorem col206_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 1 v) = true := by decide +kernel
theorem col206_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 2 v) = true := by decide +kernel
theorem s206_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 0 = true := by decide +kernel
theorem s206_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 1 = true := by decide +kernel
theorem s206_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 2 = true := by decide +kernel
theorem k206_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k206_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k206_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s206_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k206_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k206_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k206_3_3_26 k h.1 (by omega)
theorem s206_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 4 = true := by decide +kernel
theorem s206_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 5 = true := by decide +kernel
theorem k206_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k206_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k206_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k206_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k206_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k206_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k206_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k206_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k206_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k206_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k206_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s206_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k206_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k206_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k206_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k206_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k206_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k206_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k206_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k206_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k206_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k206_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k206_3_6_130 k h.1 (by omega)
theorem s206_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 3 7 = true := by decide +kernel
theorem s206_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 0 = true := by decide +kernel
theorem s206_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 1 = true := by decide +kernel
theorem s206_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 2 = true := by decide +kernel
theorem s206_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 3 = true := by decide +kernel
theorem s206_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 4 = true := by decide +kernel
theorem s206_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 5 = true := by decide +kernel
theorem k206_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k206_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k206_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k206_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k206_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k206_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k206_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s206_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k206_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k206_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k206_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k206_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k206_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k206_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k206_4_6_126 k h.1 (by omega)
theorem s206_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 4 7 = true := by decide +kernel
theorem s206_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 0 = true := by decide +kernel
theorem s206_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 1 = true := by decide +kernel
theorem s206_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 2 = true := by decide +kernel
theorem s206_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 3 = true := by decide +kernel
theorem s206_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 4 = true := by decide +kernel
theorem s206_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 5 = true := by decide +kernel
theorem k206_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k206_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k206_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k206_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k206_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k206_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k206_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s206_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k206_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k206_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k206_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k206_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k206_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k206_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 206) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (206 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k206_5_6_126 k h.1 (by omega)
theorem s206_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 5 7 = true := by decide +kernel
theorem s206_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 0 = true := by decide +kernel
theorem s206_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 1 = true := by decide +kernel
theorem s206_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 2 = true := by decide +kernel
theorem s206_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 3 = true := by decide +kernel
theorem s206_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 4 = true := by decide +kernel
theorem s206_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 5 = true := by decide +kernel
theorem s206_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 6 = true := by decide +kernel
theorem k206_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k206_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k206_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k206_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k206_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s206_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k206_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k206_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k206_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k206_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 206) ((InDA1.TCasaD 6 6 7).getD (206 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k206_6_7_12 k h.1 (by omega)
theorem col206_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 7 v) = true := by decide +kernel
theorem col206 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 206) 206 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col206_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col206_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col206_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s206_3_0
    · exact s206_3_1
    · exact s206_3_2
    · exact s206_3_3
    · exact s206_3_4
    · exact s206_3_5
    · exact s206_3_6
    · exact s206_3_7
  · fin_cases v
    · exact s206_4_0
    · exact s206_4_1
    · exact s206_4_2
    · exact s206_4_3
    · exact s206_4_4
    · exact s206_4_5
    · exact s206_4_6
    · exact s206_4_7
  · fin_cases v
    · exact s206_5_0
    · exact s206_5_1
    · exact s206_5_2
    · exact s206_5_3
    · exact s206_5_4
    · exact s206_5_5
    · exact s206_5_6
    · exact s206_5_7
  · fin_cases v
    · exact s206_6_0
    · exact s206_6_1
    · exact s206_6_2
    · exact s206_6_3
    · exact s206_6_4
    · exact s206_6_5
    · exact s206_6_6
    · exact s206_6_7
  · exact List.all_eq_true.mp col206_7 v (List.mem_finRange v)
theorem col207_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 0 v) = true := by decide +kernel
theorem col207_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 1 v) = true := by decide +kernel
theorem col207_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 2 v) = true := by decide +kernel
theorem s207_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 0 = true := by decide +kernel
theorem s207_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 1 = true := by decide +kernel
theorem s207_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 2 = true := by decide +kernel
theorem k207_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k207_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k207_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s207_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k207_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k207_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k207_3_3_26 k h.1 (by omega)
theorem s207_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 4 = true := by decide +kernel
theorem s207_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 5 = true := by decide +kernel
theorem k207_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k207_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k207_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k207_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k207_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k207_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k207_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k207_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k207_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k207_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k207_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s207_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k207_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k207_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k207_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k207_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k207_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k207_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k207_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k207_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k207_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k207_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k207_3_6_130 k h.1 (by omega)
theorem s207_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 3 7 = true := by decide +kernel
theorem s207_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 0 = true := by decide +kernel
theorem s207_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 1 = true := by decide +kernel
theorem s207_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 2 = true := by decide +kernel
theorem s207_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 3 = true := by decide +kernel
theorem s207_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 4 = true := by decide +kernel
theorem s207_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 5 = true := by decide +kernel
theorem k207_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k207_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k207_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k207_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k207_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k207_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k207_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s207_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k207_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k207_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k207_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k207_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k207_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k207_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k207_4_6_126 k h.1 (by omega)
theorem s207_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 4 7 = true := by decide +kernel
theorem s207_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 0 = true := by decide +kernel
theorem s207_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 1 = true := by decide +kernel
theorem s207_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 2 = true := by decide +kernel
theorem s207_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 3 = true := by decide +kernel
theorem s207_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 4 = true := by decide +kernel
theorem s207_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 5 = true := by decide +kernel
theorem k207_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k207_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k207_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k207_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k207_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k207_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k207_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s207_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k207_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k207_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k207_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k207_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k207_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k207_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 207) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (207 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k207_5_6_126 k h.1 (by omega)
theorem s207_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 5 7 = true := by decide +kernel
theorem s207_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 0 = true := by decide +kernel
theorem s207_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 1 = true := by decide +kernel
theorem s207_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 2 = true := by decide +kernel
theorem s207_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 3 = true := by decide +kernel
theorem s207_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 4 = true := by decide +kernel
theorem s207_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 5 = true := by decide +kernel
theorem s207_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 6 = true := by decide +kernel
theorem k207_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k207_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k207_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k207_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k207_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s207_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k207_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k207_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k207_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k207_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 207) ((InDA1.TCasaD 6 6 7).getD (207 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k207_6_7_12 k h.1 (by omega)
theorem col207_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 7 v) = true := by decide +kernel
theorem col207 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 207) 207 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col207_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col207_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col207_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s207_3_0
    · exact s207_3_1
    · exact s207_3_2
    · exact s207_3_3
    · exact s207_3_4
    · exact s207_3_5
    · exact s207_3_6
    · exact s207_3_7
  · fin_cases v
    · exact s207_4_0
    · exact s207_4_1
    · exact s207_4_2
    · exact s207_4_3
    · exact s207_4_4
    · exact s207_4_5
    · exact s207_4_6
    · exact s207_4_7
  · fin_cases v
    · exact s207_5_0
    · exact s207_5_1
    · exact s207_5_2
    · exact s207_5_3
    · exact s207_5_4
    · exact s207_5_5
    · exact s207_5_6
    · exact s207_5_7
  · fin_cases v
    · exact s207_6_0
    · exact s207_6_1
    · exact s207_6_2
    · exact s207_6_3
    · exact s207_6_4
    · exact s207_6_5
    · exact s207_6_6
    · exact s207_6_7
  · exact List.all_eq_true.mp col207_7 v (List.mem_finRange v)
theorem col208_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 0 v) = true := by decide +kernel
theorem col208_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 1 v) = true := by decide +kernel
theorem col208_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 2 v) = true := by decide +kernel
theorem s208_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 0 = true := by decide +kernel
theorem s208_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 1 = true := by decide +kernel
theorem s208_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 2 = true := by decide +kernel
theorem k208_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k208_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k208_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s208_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k208_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k208_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k208_3_3_26 k h.1 (by omega)
theorem s208_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 4 = true := by decide +kernel
theorem s208_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 5 = true := by decide +kernel
theorem k208_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k208_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k208_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k208_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k208_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k208_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k208_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k208_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k208_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k208_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k208_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s208_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k208_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k208_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k208_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k208_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k208_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k208_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k208_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k208_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k208_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k208_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k208_3_6_130 k h.1 (by omega)
theorem s208_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 3 7 = true := by decide +kernel
theorem s208_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 0 = true := by decide +kernel
theorem s208_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 1 = true := by decide +kernel
theorem s208_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 2 = true := by decide +kernel
theorem s208_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 3 = true := by decide +kernel
theorem s208_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 4 = true := by decide +kernel
theorem s208_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 5 = true := by decide +kernel
theorem k208_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k208_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k208_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k208_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k208_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k208_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k208_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s208_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k208_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k208_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k208_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k208_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k208_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k208_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k208_4_6_126 k h.1 (by omega)
theorem s208_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 4 7 = true := by decide +kernel
theorem s208_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 0 = true := by decide +kernel
theorem s208_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 1 = true := by decide +kernel
theorem s208_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 2 = true := by decide +kernel
theorem s208_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 3 = true := by decide +kernel
theorem s208_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 4 = true := by decide +kernel
theorem s208_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 5 = true := by decide +kernel
theorem k208_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k208_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k208_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k208_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k208_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k208_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k208_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s208_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k208_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k208_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k208_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k208_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k208_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k208_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 208) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (208 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k208_5_6_126 k h.1 (by omega)
theorem s208_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 5 7 = true := by decide +kernel
theorem s208_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 0 = true := by decide +kernel
theorem s208_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 1 = true := by decide +kernel
theorem s208_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 2 = true := by decide +kernel
theorem s208_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 3 = true := by decide +kernel
theorem s208_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 4 = true := by decide +kernel
theorem s208_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 5 = true := by decide +kernel
theorem s208_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 6 = true := by decide +kernel
theorem k208_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k208_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k208_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k208_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k208_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s208_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k208_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k208_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k208_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k208_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 208) ((InDA1.TCasaD 6 6 7).getD (208 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k208_6_7_12 k h.1 (by omega)
theorem col208_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 7 v) = true := by decide +kernel
theorem col208 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 208) 208 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col208_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col208_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col208_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s208_3_0
    · exact s208_3_1
    · exact s208_3_2
    · exact s208_3_3
    · exact s208_3_4
    · exact s208_3_5
    · exact s208_3_6
    · exact s208_3_7
  · fin_cases v
    · exact s208_4_0
    · exact s208_4_1
    · exact s208_4_2
    · exact s208_4_3
    · exact s208_4_4
    · exact s208_4_5
    · exact s208_4_6
    · exact s208_4_7
  · fin_cases v
    · exact s208_5_0
    · exact s208_5_1
    · exact s208_5_2
    · exact s208_5_3
    · exact s208_5_4
    · exact s208_5_5
    · exact s208_5_6
    · exact s208_5_7
  · fin_cases v
    · exact s208_6_0
    · exact s208_6_1
    · exact s208_6_2
    · exact s208_6_3
    · exact s208_6_4
    · exact s208_6_5
    · exact s208_6_6
    · exact s208_6_7
  · exact List.all_eq_true.mp col208_7 v (List.mem_finRange v)
theorem col209_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 0 v) = true := by decide +kernel
theorem col209_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 1 v) = true := by decide +kernel
theorem col209_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 2 v) = true := by decide +kernel
theorem s209_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 0 = true := by decide +kernel
theorem s209_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 1 = true := by decide +kernel
theorem s209_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 2 = true := by decide +kernel
theorem k209_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k209_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k209_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s209_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k209_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k209_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k209_3_3_26 k h.1 (by omega)
theorem s209_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 4 = true := by decide +kernel
theorem s209_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 5 = true := by decide +kernel
theorem k209_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k209_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k209_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k209_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k209_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k209_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k209_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k209_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k209_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k209_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k209_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s209_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k209_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k209_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k209_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k209_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k209_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k209_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k209_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k209_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k209_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k209_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k209_3_6_130 k h.1 (by omega)
theorem s209_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 3 7 = true := by decide +kernel
theorem s209_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 0 = true := by decide +kernel
theorem s209_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 1 = true := by decide +kernel
theorem s209_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 2 = true := by decide +kernel
theorem s209_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 3 = true := by decide +kernel
theorem s209_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 4 = true := by decide +kernel
theorem s209_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 5 = true := by decide +kernel
theorem k209_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k209_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k209_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k209_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k209_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k209_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k209_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s209_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k209_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k209_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k209_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k209_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k209_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k209_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k209_4_6_126 k h.1 (by omega)
theorem s209_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 4 7 = true := by decide +kernel
theorem s209_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 0 = true := by decide +kernel
theorem s209_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 1 = true := by decide +kernel
theorem s209_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 2 = true := by decide +kernel
theorem s209_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 3 = true := by decide +kernel
theorem s209_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 4 = true := by decide +kernel
theorem s209_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 5 = true := by decide +kernel
theorem k209_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k209_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k209_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k209_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k209_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k209_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k209_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s209_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k209_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k209_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k209_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k209_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k209_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k209_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 209) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (209 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k209_5_6_126 k h.1 (by omega)
theorem s209_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 5 7 = true := by decide +kernel
theorem s209_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 0 = true := by decide +kernel
theorem s209_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 1 = true := by decide +kernel
theorem s209_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 2 = true := by decide +kernel
theorem s209_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 3 = true := by decide +kernel
theorem s209_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 4 = true := by decide +kernel
theorem s209_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 5 = true := by decide +kernel
theorem s209_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 6 = true := by decide +kernel
theorem k209_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k209_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k209_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k209_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k209_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s209_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k209_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k209_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k209_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k209_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 209) ((InDA1.TCasaD 6 6 7).getD (209 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k209_6_7_12 k h.1 (by omega)
theorem col209_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 7 v) = true := by decide +kernel
theorem col209 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 209) 209 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col209_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col209_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col209_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s209_3_0
    · exact s209_3_1
    · exact s209_3_2
    · exact s209_3_3
    · exact s209_3_4
    · exact s209_3_5
    · exact s209_3_6
    · exact s209_3_7
  · fin_cases v
    · exact s209_4_0
    · exact s209_4_1
    · exact s209_4_2
    · exact s209_4_3
    · exact s209_4_4
    · exact s209_4_5
    · exact s209_4_6
    · exact s209_4_7
  · fin_cases v
    · exact s209_5_0
    · exact s209_5_1
    · exact s209_5_2
    · exact s209_5_3
    · exact s209_5_4
    · exact s209_5_5
    · exact s209_5_6
    · exact s209_5_7
  · fin_cases v
    · exact s209_6_0
    · exact s209_6_1
    · exact s209_6_2
    · exact s209_6_3
    · exact s209_6_4
    · exact s209_6_5
    · exact s209_6_6
    · exact s209_6_7
  · exact List.all_eq_true.mp col209_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
