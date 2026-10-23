module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [200, 205). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col200_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 0 v) = true := by decide +kernel
theorem col200_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 1 v) = true := by decide +kernel
theorem col200_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 2 v) = true := by decide +kernel
theorem s200_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 0 = true := by decide +kernel
theorem s200_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 1 = true := by decide +kernel
theorem s200_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 2 = true := by decide +kernel
theorem k200_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k200_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k200_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s200_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k200_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k200_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k200_3_3_26 k h.1 (by omega)
theorem s200_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 4 = true := by decide +kernel
theorem s200_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 5 = true := by decide +kernel
theorem k200_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k200_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k200_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k200_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k200_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k200_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k200_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k200_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k200_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k200_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k200_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s200_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k200_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k200_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k200_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k200_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k200_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k200_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k200_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k200_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k200_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k200_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k200_3_6_130 k h.1 (by omega)
theorem s200_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 3 7 = true := by decide +kernel
theorem s200_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 0 = true := by decide +kernel
theorem s200_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 1 = true := by decide +kernel
theorem s200_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 2 = true := by decide +kernel
theorem s200_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 3 = true := by decide +kernel
theorem s200_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 4 = true := by decide +kernel
theorem s200_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 5 = true := by decide +kernel
theorem k200_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k200_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k200_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k200_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k200_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k200_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k200_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s200_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k200_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k200_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k200_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k200_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k200_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k200_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k200_4_6_126 k h.1 (by omega)
theorem s200_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 4 7 = true := by decide +kernel
theorem s200_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 0 = true := by decide +kernel
theorem s200_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 1 = true := by decide +kernel
theorem s200_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 2 = true := by decide +kernel
theorem s200_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 3 = true := by decide +kernel
theorem s200_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 4 = true := by decide +kernel
theorem s200_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 5 = true := by decide +kernel
theorem k200_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k200_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k200_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k200_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k200_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k200_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k200_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s200_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k200_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k200_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k200_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k200_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k200_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k200_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 200) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (200 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k200_5_6_126 k h.1 (by omega)
theorem s200_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 5 7 = true := by decide +kernel
theorem s200_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 0 = true := by decide +kernel
theorem s200_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 1 = true := by decide +kernel
theorem s200_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 2 = true := by decide +kernel
theorem s200_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 3 = true := by decide +kernel
theorem s200_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 4 = true := by decide +kernel
theorem s200_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 5 = true := by decide +kernel
theorem s200_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 6 = true := by decide +kernel
theorem k200_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k200_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k200_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k200_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k200_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s200_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k200_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k200_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k200_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k200_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 200) ((InDA1.TCasaD 6 6 7).getD (200 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k200_6_7_12 k h.1 (by omega)
theorem col200_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 7 v) = true := by decide +kernel
theorem col200 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 200) 200 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col200_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col200_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col200_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s200_3_0
    · exact s200_3_1
    · exact s200_3_2
    · exact s200_3_3
    · exact s200_3_4
    · exact s200_3_5
    · exact s200_3_6
    · exact s200_3_7
  · fin_cases v
    · exact s200_4_0
    · exact s200_4_1
    · exact s200_4_2
    · exact s200_4_3
    · exact s200_4_4
    · exact s200_4_5
    · exact s200_4_6
    · exact s200_4_7
  · fin_cases v
    · exact s200_5_0
    · exact s200_5_1
    · exact s200_5_2
    · exact s200_5_3
    · exact s200_5_4
    · exact s200_5_5
    · exact s200_5_6
    · exact s200_5_7
  · fin_cases v
    · exact s200_6_0
    · exact s200_6_1
    · exact s200_6_2
    · exact s200_6_3
    · exact s200_6_4
    · exact s200_6_5
    · exact s200_6_6
    · exact s200_6_7
  · exact List.all_eq_true.mp col200_7 v (List.mem_finRange v)
theorem col201_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 0 v) = true := by decide +kernel
theorem col201_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 1 v) = true := by decide +kernel
theorem col201_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 2 v) = true := by decide +kernel
theorem s201_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 0 = true := by decide +kernel
theorem s201_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 1 = true := by decide +kernel
theorem s201_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 2 = true := by decide +kernel
theorem k201_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k201_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k201_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s201_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k201_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k201_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k201_3_3_26 k h.1 (by omega)
theorem s201_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 4 = true := by decide +kernel
theorem s201_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 5 = true := by decide +kernel
theorem k201_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k201_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k201_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k201_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k201_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k201_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k201_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k201_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k201_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k201_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k201_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s201_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k201_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k201_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k201_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k201_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k201_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k201_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k201_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k201_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k201_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k201_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k201_3_6_130 k h.1 (by omega)
theorem s201_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 3 7 = true := by decide +kernel
theorem s201_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 0 = true := by decide +kernel
theorem s201_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 1 = true := by decide +kernel
theorem s201_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 2 = true := by decide +kernel
theorem s201_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 3 = true := by decide +kernel
theorem s201_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 4 = true := by decide +kernel
theorem s201_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 5 = true := by decide +kernel
theorem k201_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k201_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k201_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k201_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k201_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k201_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k201_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s201_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k201_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k201_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k201_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k201_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k201_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k201_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k201_4_6_126 k h.1 (by omega)
theorem s201_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 4 7 = true := by decide +kernel
theorem s201_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 0 = true := by decide +kernel
theorem s201_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 1 = true := by decide +kernel
theorem s201_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 2 = true := by decide +kernel
theorem s201_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 3 = true := by decide +kernel
theorem s201_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 4 = true := by decide +kernel
theorem s201_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 5 = true := by decide +kernel
theorem k201_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k201_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k201_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k201_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k201_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k201_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k201_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s201_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k201_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k201_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k201_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k201_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k201_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k201_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 201) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (201 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k201_5_6_126 k h.1 (by omega)
theorem s201_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 5 7 = true := by decide +kernel
theorem s201_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 0 = true := by decide +kernel
theorem s201_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 1 = true := by decide +kernel
theorem s201_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 2 = true := by decide +kernel
theorem s201_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 3 = true := by decide +kernel
theorem s201_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 4 = true := by decide +kernel
theorem s201_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 5 = true := by decide +kernel
theorem s201_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 6 = true := by decide +kernel
theorem k201_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k201_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k201_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k201_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k201_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s201_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k201_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k201_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k201_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k201_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 201) ((InDA1.TCasaD 6 6 7).getD (201 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k201_6_7_12 k h.1 (by omega)
theorem col201_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 7 v) = true := by decide +kernel
theorem col201 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 201) 201 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col201_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col201_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col201_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s201_3_0
    · exact s201_3_1
    · exact s201_3_2
    · exact s201_3_3
    · exact s201_3_4
    · exact s201_3_5
    · exact s201_3_6
    · exact s201_3_7
  · fin_cases v
    · exact s201_4_0
    · exact s201_4_1
    · exact s201_4_2
    · exact s201_4_3
    · exact s201_4_4
    · exact s201_4_5
    · exact s201_4_6
    · exact s201_4_7
  · fin_cases v
    · exact s201_5_0
    · exact s201_5_1
    · exact s201_5_2
    · exact s201_5_3
    · exact s201_5_4
    · exact s201_5_5
    · exact s201_5_6
    · exact s201_5_7
  · fin_cases v
    · exact s201_6_0
    · exact s201_6_1
    · exact s201_6_2
    · exact s201_6_3
    · exact s201_6_4
    · exact s201_6_5
    · exact s201_6_6
    · exact s201_6_7
  · exact List.all_eq_true.mp col201_7 v (List.mem_finRange v)
theorem col202_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 0 v) = true := by decide +kernel
theorem col202_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 1 v) = true := by decide +kernel
theorem col202_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 2 v) = true := by decide +kernel
theorem s202_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 0 = true := by decide +kernel
theorem s202_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 1 = true := by decide +kernel
theorem s202_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 2 = true := by decide +kernel
theorem k202_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k202_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k202_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s202_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k202_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k202_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k202_3_3_26 k h.1 (by omega)
theorem s202_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 4 = true := by decide +kernel
theorem s202_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 5 = true := by decide +kernel
theorem k202_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k202_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k202_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k202_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k202_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k202_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k202_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k202_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k202_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k202_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k202_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s202_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k202_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k202_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k202_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k202_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k202_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k202_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k202_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k202_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k202_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k202_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k202_3_6_130 k h.1 (by omega)
theorem s202_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 3 7 = true := by decide +kernel
theorem s202_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 0 = true := by decide +kernel
theorem s202_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 1 = true := by decide +kernel
theorem s202_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 2 = true := by decide +kernel
theorem s202_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 3 = true := by decide +kernel
theorem s202_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 4 = true := by decide +kernel
theorem s202_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 5 = true := by decide +kernel
theorem k202_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k202_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k202_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k202_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k202_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k202_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k202_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s202_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k202_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k202_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k202_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k202_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k202_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k202_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k202_4_6_126 k h.1 (by omega)
theorem s202_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 4 7 = true := by decide +kernel
theorem s202_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 0 = true := by decide +kernel
theorem s202_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 1 = true := by decide +kernel
theorem s202_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 2 = true := by decide +kernel
theorem s202_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 3 = true := by decide +kernel
theorem s202_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 4 = true := by decide +kernel
theorem s202_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 5 = true := by decide +kernel
theorem k202_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k202_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k202_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k202_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k202_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k202_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k202_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s202_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k202_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k202_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k202_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k202_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k202_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k202_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 202) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (202 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k202_5_6_126 k h.1 (by omega)
theorem s202_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 5 7 = true := by decide +kernel
theorem s202_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 0 = true := by decide +kernel
theorem s202_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 1 = true := by decide +kernel
theorem s202_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 2 = true := by decide +kernel
theorem s202_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 3 = true := by decide +kernel
theorem s202_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 4 = true := by decide +kernel
theorem s202_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 5 = true := by decide +kernel
theorem s202_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 6 = true := by decide +kernel
theorem k202_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k202_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k202_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k202_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k202_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s202_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k202_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k202_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k202_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k202_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 202) ((InDA1.TCasaD 6 6 7).getD (202 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k202_6_7_12 k h.1 (by omega)
theorem col202_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 7 v) = true := by decide +kernel
theorem col202 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 202) 202 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col202_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col202_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col202_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s202_3_0
    · exact s202_3_1
    · exact s202_3_2
    · exact s202_3_3
    · exact s202_3_4
    · exact s202_3_5
    · exact s202_3_6
    · exact s202_3_7
  · fin_cases v
    · exact s202_4_0
    · exact s202_4_1
    · exact s202_4_2
    · exact s202_4_3
    · exact s202_4_4
    · exact s202_4_5
    · exact s202_4_6
    · exact s202_4_7
  · fin_cases v
    · exact s202_5_0
    · exact s202_5_1
    · exact s202_5_2
    · exact s202_5_3
    · exact s202_5_4
    · exact s202_5_5
    · exact s202_5_6
    · exact s202_5_7
  · fin_cases v
    · exact s202_6_0
    · exact s202_6_1
    · exact s202_6_2
    · exact s202_6_3
    · exact s202_6_4
    · exact s202_6_5
    · exact s202_6_6
    · exact s202_6_7
  · exact List.all_eq_true.mp col202_7 v (List.mem_finRange v)
theorem col203_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 0 v) = true := by decide +kernel
theorem col203_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 1 v) = true := by decide +kernel
theorem col203_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 2 v) = true := by decide +kernel
theorem s203_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 0 = true := by decide +kernel
theorem s203_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 1 = true := by decide +kernel
theorem s203_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 2 = true := by decide +kernel
theorem k203_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k203_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k203_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s203_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k203_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k203_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k203_3_3_26 k h.1 (by omega)
theorem s203_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 4 = true := by decide +kernel
theorem s203_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 5 = true := by decide +kernel
theorem k203_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k203_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k203_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k203_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k203_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k203_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k203_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k203_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k203_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k203_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k203_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s203_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k203_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k203_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k203_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k203_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k203_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k203_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k203_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k203_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k203_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k203_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k203_3_6_130 k h.1 (by omega)
theorem s203_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 3 7 = true := by decide +kernel
theorem s203_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 0 = true := by decide +kernel
theorem s203_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 1 = true := by decide +kernel
theorem s203_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 2 = true := by decide +kernel
theorem s203_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 3 = true := by decide +kernel
theorem s203_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 4 = true := by decide +kernel
theorem s203_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 5 = true := by decide +kernel
theorem k203_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k203_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k203_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k203_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k203_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k203_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k203_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s203_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k203_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k203_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k203_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k203_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k203_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k203_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k203_4_6_126 k h.1 (by omega)
theorem s203_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 4 7 = true := by decide +kernel
theorem s203_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 0 = true := by decide +kernel
theorem s203_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 1 = true := by decide +kernel
theorem s203_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 2 = true := by decide +kernel
theorem s203_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 3 = true := by decide +kernel
theorem s203_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 4 = true := by decide +kernel
theorem s203_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 5 = true := by decide +kernel
theorem k203_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k203_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k203_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k203_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k203_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k203_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k203_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s203_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k203_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k203_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k203_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k203_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k203_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k203_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 203) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (203 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k203_5_6_126 k h.1 (by omega)
theorem s203_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 5 7 = true := by decide +kernel
theorem s203_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 0 = true := by decide +kernel
theorem s203_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 1 = true := by decide +kernel
theorem s203_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 2 = true := by decide +kernel
theorem s203_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 3 = true := by decide +kernel
theorem s203_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 4 = true := by decide +kernel
theorem s203_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 5 = true := by decide +kernel
theorem s203_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 6 = true := by decide +kernel
theorem k203_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k203_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k203_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k203_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k203_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s203_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k203_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k203_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k203_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k203_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 203) ((InDA1.TCasaD 6 6 7).getD (203 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k203_6_7_12 k h.1 (by omega)
theorem col203_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 7 v) = true := by decide +kernel
theorem col203 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 203) 203 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col203_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col203_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col203_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s203_3_0
    · exact s203_3_1
    · exact s203_3_2
    · exact s203_3_3
    · exact s203_3_4
    · exact s203_3_5
    · exact s203_3_6
    · exact s203_3_7
  · fin_cases v
    · exact s203_4_0
    · exact s203_4_1
    · exact s203_4_2
    · exact s203_4_3
    · exact s203_4_4
    · exact s203_4_5
    · exact s203_4_6
    · exact s203_4_7
  · fin_cases v
    · exact s203_5_0
    · exact s203_5_1
    · exact s203_5_2
    · exact s203_5_3
    · exact s203_5_4
    · exact s203_5_5
    · exact s203_5_6
    · exact s203_5_7
  · fin_cases v
    · exact s203_6_0
    · exact s203_6_1
    · exact s203_6_2
    · exact s203_6_3
    · exact s203_6_4
    · exact s203_6_5
    · exact s203_6_6
    · exact s203_6_7
  · exact List.all_eq_true.mp col203_7 v (List.mem_finRange v)
theorem col204_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 0 v) = true := by decide +kernel
theorem col204_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 1 v) = true := by decide +kernel
theorem col204_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 2 v) = true := by decide +kernel
theorem s204_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 0 = true := by decide +kernel
theorem s204_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 1 = true := by decide +kernel
theorem s204_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 2 = true := by decide +kernel
theorem k204_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k204_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k204_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s204_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k204_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k204_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k204_3_3_26 k h.1 (by omega)
theorem s204_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 4 = true := by decide +kernel
theorem s204_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 5 = true := by decide +kernel
theorem k204_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k204_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k204_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k204_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k204_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k204_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k204_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k204_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k204_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k204_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k204_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s204_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k204_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k204_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k204_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k204_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k204_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k204_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k204_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k204_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k204_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k204_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k204_3_6_130 k h.1 (by omega)
theorem s204_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 3 7 = true := by decide +kernel
theorem s204_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 0 = true := by decide +kernel
theorem s204_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 1 = true := by decide +kernel
theorem s204_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 2 = true := by decide +kernel
theorem s204_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 3 = true := by decide +kernel
theorem s204_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 4 = true := by decide +kernel
theorem s204_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 5 = true := by decide +kernel
theorem k204_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k204_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k204_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k204_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k204_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k204_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k204_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s204_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k204_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k204_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k204_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k204_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k204_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k204_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k204_4_6_126 k h.1 (by omega)
theorem s204_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 4 7 = true := by decide +kernel
theorem s204_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 0 = true := by decide +kernel
theorem s204_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 1 = true := by decide +kernel
theorem s204_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 2 = true := by decide +kernel
theorem s204_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 3 = true := by decide +kernel
theorem s204_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 4 = true := by decide +kernel
theorem s204_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 5 = true := by decide +kernel
theorem k204_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k204_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k204_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k204_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k204_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k204_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k204_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s204_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k204_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k204_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k204_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k204_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k204_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k204_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 204) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (204 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k204_5_6_126 k h.1 (by omega)
theorem s204_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 5 7 = true := by decide +kernel
theorem s204_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 0 = true := by decide +kernel
theorem s204_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 1 = true := by decide +kernel
theorem s204_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 2 = true := by decide +kernel
theorem s204_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 3 = true := by decide +kernel
theorem s204_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 4 = true := by decide +kernel
theorem s204_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 5 = true := by decide +kernel
theorem s204_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 6 = true := by decide +kernel
theorem k204_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k204_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k204_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k204_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k204_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s204_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k204_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k204_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k204_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k204_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 204) ((InDA1.TCasaD 6 6 7).getD (204 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k204_6_7_12 k h.1 (by omega)
theorem col204_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 7 v) = true := by decide +kernel
theorem col204 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 204) 204 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col204_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col204_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col204_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s204_3_0
    · exact s204_3_1
    · exact s204_3_2
    · exact s204_3_3
    · exact s204_3_4
    · exact s204_3_5
    · exact s204_3_6
    · exact s204_3_7
  · fin_cases v
    · exact s204_4_0
    · exact s204_4_1
    · exact s204_4_2
    · exact s204_4_3
    · exact s204_4_4
    · exact s204_4_5
    · exact s204_4_6
    · exact s204_4_7
  · fin_cases v
    · exact s204_5_0
    · exact s204_5_1
    · exact s204_5_2
    · exact s204_5_3
    · exact s204_5_4
    · exact s204_5_5
    · exact s204_5_6
    · exact s204_5_7
  · fin_cases v
    · exact s204_6_0
    · exact s204_6_1
    · exact s204_6_2
    · exact s204_6_3
    · exact s204_6_4
    · exact s204_6_5
    · exact s204_6_6
    · exact s204_6_7
  · exact List.all_eq_true.mp col204_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
