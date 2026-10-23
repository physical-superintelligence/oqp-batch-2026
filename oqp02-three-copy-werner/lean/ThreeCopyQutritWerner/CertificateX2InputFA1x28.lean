module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [140, 145). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col140_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 0 v) = true := by decide +kernel
theorem col140_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 1 v) = true := by decide +kernel
theorem col140_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 2 v) = true := by decide +kernel
theorem s140_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 0 = true := by decide +kernel
theorem s140_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 1 = true := by decide +kernel
theorem s140_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 2 = true := by decide +kernel
theorem k140_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k140_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k140_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s140_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k140_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k140_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k140_3_3_26 k h.1 (by omega)
theorem s140_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 4 = true := by decide +kernel
theorem s140_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 5 = true := by decide +kernel
theorem k140_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k140_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k140_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k140_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k140_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k140_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k140_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k140_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k140_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k140_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k140_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s140_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k140_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k140_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k140_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k140_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k140_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k140_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k140_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k140_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k140_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k140_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k140_3_6_130 k h.1 (by omega)
theorem s140_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 3 7 = true := by decide +kernel
theorem s140_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 0 = true := by decide +kernel
theorem s140_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 1 = true := by decide +kernel
theorem s140_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 2 = true := by decide +kernel
theorem s140_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 3 = true := by decide +kernel
theorem s140_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 4 = true := by decide +kernel
theorem s140_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 5 = true := by decide +kernel
theorem k140_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k140_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k140_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k140_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k140_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k140_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k140_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s140_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k140_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k140_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k140_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k140_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k140_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k140_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k140_4_6_126 k h.1 (by omega)
theorem s140_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 4 7 = true := by decide +kernel
theorem s140_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 0 = true := by decide +kernel
theorem s140_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 1 = true := by decide +kernel
theorem s140_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 2 = true := by decide +kernel
theorem s140_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 3 = true := by decide +kernel
theorem s140_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 4 = true := by decide +kernel
theorem s140_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 5 = true := by decide +kernel
theorem k140_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k140_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k140_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k140_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k140_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k140_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k140_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s140_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k140_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k140_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k140_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k140_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k140_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k140_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 140) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (140 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k140_5_6_126 k h.1 (by omega)
theorem s140_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 5 7 = true := by decide +kernel
theorem s140_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 0 = true := by decide +kernel
theorem s140_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 1 = true := by decide +kernel
theorem s140_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 2 = true := by decide +kernel
theorem s140_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 3 = true := by decide +kernel
theorem s140_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 4 = true := by decide +kernel
theorem s140_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 5 = true := by decide +kernel
theorem s140_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 6 = true := by decide +kernel
theorem k140_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k140_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k140_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k140_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k140_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s140_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k140_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k140_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k140_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k140_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 140) ((InDA1.TCasaD 6 6 7).getD (140 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k140_6_7_12 k h.1 (by omega)
theorem col140_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 7 v) = true := by decide +kernel
theorem col140 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 140) 140 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col140_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col140_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col140_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s140_3_0
    · exact s140_3_1
    · exact s140_3_2
    · exact s140_3_3
    · exact s140_3_4
    · exact s140_3_5
    · exact s140_3_6
    · exact s140_3_7
  · fin_cases v
    · exact s140_4_0
    · exact s140_4_1
    · exact s140_4_2
    · exact s140_4_3
    · exact s140_4_4
    · exact s140_4_5
    · exact s140_4_6
    · exact s140_4_7
  · fin_cases v
    · exact s140_5_0
    · exact s140_5_1
    · exact s140_5_2
    · exact s140_5_3
    · exact s140_5_4
    · exact s140_5_5
    · exact s140_5_6
    · exact s140_5_7
  · fin_cases v
    · exact s140_6_0
    · exact s140_6_1
    · exact s140_6_2
    · exact s140_6_3
    · exact s140_6_4
    · exact s140_6_5
    · exact s140_6_6
    · exact s140_6_7
  · exact List.all_eq_true.mp col140_7 v (List.mem_finRange v)
theorem col141_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 0 v) = true := by decide +kernel
theorem col141_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 1 v) = true := by decide +kernel
theorem col141_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 2 v) = true := by decide +kernel
theorem s141_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 0 = true := by decide +kernel
theorem s141_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 1 = true := by decide +kernel
theorem s141_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 2 = true := by decide +kernel
theorem k141_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k141_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k141_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s141_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k141_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k141_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k141_3_3_26 k h.1 (by omega)
theorem s141_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 4 = true := by decide +kernel
theorem s141_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 5 = true := by decide +kernel
theorem k141_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k141_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k141_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k141_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k141_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k141_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k141_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k141_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k141_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k141_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k141_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s141_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k141_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k141_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k141_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k141_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k141_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k141_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k141_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k141_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k141_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k141_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k141_3_6_130 k h.1 (by omega)
theorem s141_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 3 7 = true := by decide +kernel
theorem s141_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 0 = true := by decide +kernel
theorem s141_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 1 = true := by decide +kernel
theorem s141_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 2 = true := by decide +kernel
theorem s141_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 3 = true := by decide +kernel
theorem s141_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 4 = true := by decide +kernel
theorem s141_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 5 = true := by decide +kernel
theorem k141_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k141_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k141_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k141_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k141_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k141_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k141_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s141_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k141_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k141_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k141_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k141_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k141_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k141_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k141_4_6_126 k h.1 (by omega)
theorem s141_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 4 7 = true := by decide +kernel
theorem s141_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 0 = true := by decide +kernel
theorem s141_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 1 = true := by decide +kernel
theorem s141_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 2 = true := by decide +kernel
theorem s141_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 3 = true := by decide +kernel
theorem s141_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 4 = true := by decide +kernel
theorem s141_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 5 = true := by decide +kernel
theorem k141_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k141_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k141_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k141_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k141_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k141_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k141_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s141_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k141_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k141_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k141_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k141_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k141_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k141_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 141) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (141 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k141_5_6_126 k h.1 (by omega)
theorem s141_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 5 7 = true := by decide +kernel
theorem s141_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 0 = true := by decide +kernel
theorem s141_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 1 = true := by decide +kernel
theorem s141_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 2 = true := by decide +kernel
theorem s141_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 3 = true := by decide +kernel
theorem s141_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 4 = true := by decide +kernel
theorem s141_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 5 = true := by decide +kernel
theorem s141_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 6 = true := by decide +kernel
theorem k141_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k141_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k141_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k141_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k141_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s141_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k141_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k141_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k141_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k141_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 141) ((InDA1.TCasaD 6 6 7).getD (141 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k141_6_7_12 k h.1 (by omega)
theorem col141_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 7 v) = true := by decide +kernel
theorem col141 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 141) 141 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col141_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col141_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col141_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s141_3_0
    · exact s141_3_1
    · exact s141_3_2
    · exact s141_3_3
    · exact s141_3_4
    · exact s141_3_5
    · exact s141_3_6
    · exact s141_3_7
  · fin_cases v
    · exact s141_4_0
    · exact s141_4_1
    · exact s141_4_2
    · exact s141_4_3
    · exact s141_4_4
    · exact s141_4_5
    · exact s141_4_6
    · exact s141_4_7
  · fin_cases v
    · exact s141_5_0
    · exact s141_5_1
    · exact s141_5_2
    · exact s141_5_3
    · exact s141_5_4
    · exact s141_5_5
    · exact s141_5_6
    · exact s141_5_7
  · fin_cases v
    · exact s141_6_0
    · exact s141_6_1
    · exact s141_6_2
    · exact s141_6_3
    · exact s141_6_4
    · exact s141_6_5
    · exact s141_6_6
    · exact s141_6_7
  · exact List.all_eq_true.mp col141_7 v (List.mem_finRange v)
theorem col142_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 0 v) = true := by decide +kernel
theorem col142_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 1 v) = true := by decide +kernel
theorem col142_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 2 v) = true := by decide +kernel
theorem s142_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 0 = true := by decide +kernel
theorem s142_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 1 = true := by decide +kernel
theorem s142_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 2 = true := by decide +kernel
theorem k142_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k142_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k142_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s142_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k142_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k142_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k142_3_3_26 k h.1 (by omega)
theorem s142_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 4 = true := by decide +kernel
theorem s142_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 5 = true := by decide +kernel
theorem k142_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k142_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k142_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k142_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k142_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k142_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k142_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k142_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k142_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k142_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k142_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s142_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k142_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k142_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k142_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k142_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k142_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k142_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k142_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k142_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k142_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k142_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k142_3_6_130 k h.1 (by omega)
theorem s142_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 3 7 = true := by decide +kernel
theorem s142_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 0 = true := by decide +kernel
theorem s142_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 1 = true := by decide +kernel
theorem s142_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 2 = true := by decide +kernel
theorem s142_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 3 = true := by decide +kernel
theorem s142_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 4 = true := by decide +kernel
theorem s142_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 5 = true := by decide +kernel
theorem k142_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k142_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k142_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k142_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k142_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k142_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k142_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s142_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k142_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k142_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k142_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k142_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k142_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k142_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k142_4_6_126 k h.1 (by omega)
theorem s142_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 4 7 = true := by decide +kernel
theorem s142_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 0 = true := by decide +kernel
theorem s142_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 1 = true := by decide +kernel
theorem s142_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 2 = true := by decide +kernel
theorem s142_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 3 = true := by decide +kernel
theorem s142_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 4 = true := by decide +kernel
theorem s142_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 5 = true := by decide +kernel
theorem k142_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k142_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k142_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k142_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k142_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k142_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k142_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s142_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k142_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k142_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k142_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k142_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k142_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k142_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 142) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (142 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k142_5_6_126 k h.1 (by omega)
theorem s142_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 5 7 = true := by decide +kernel
theorem s142_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 0 = true := by decide +kernel
theorem s142_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 1 = true := by decide +kernel
theorem s142_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 2 = true := by decide +kernel
theorem s142_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 3 = true := by decide +kernel
theorem s142_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 4 = true := by decide +kernel
theorem s142_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 5 = true := by decide +kernel
theorem s142_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 6 = true := by decide +kernel
theorem k142_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k142_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k142_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k142_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k142_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s142_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k142_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k142_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k142_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k142_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 142) ((InDA1.TCasaD 6 6 7).getD (142 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k142_6_7_12 k h.1 (by omega)
theorem col142_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 7 v) = true := by decide +kernel
theorem col142 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 142) 142 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col142_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col142_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col142_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s142_3_0
    · exact s142_3_1
    · exact s142_3_2
    · exact s142_3_3
    · exact s142_3_4
    · exact s142_3_5
    · exact s142_3_6
    · exact s142_3_7
  · fin_cases v
    · exact s142_4_0
    · exact s142_4_1
    · exact s142_4_2
    · exact s142_4_3
    · exact s142_4_4
    · exact s142_4_5
    · exact s142_4_6
    · exact s142_4_7
  · fin_cases v
    · exact s142_5_0
    · exact s142_5_1
    · exact s142_5_2
    · exact s142_5_3
    · exact s142_5_4
    · exact s142_5_5
    · exact s142_5_6
    · exact s142_5_7
  · fin_cases v
    · exact s142_6_0
    · exact s142_6_1
    · exact s142_6_2
    · exact s142_6_3
    · exact s142_6_4
    · exact s142_6_5
    · exact s142_6_6
    · exact s142_6_7
  · exact List.all_eq_true.mp col142_7 v (List.mem_finRange v)
theorem col143_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 0 v) = true := by decide +kernel
theorem col143_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 1 v) = true := by decide +kernel
theorem col143_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 2 v) = true := by decide +kernel
theorem s143_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 0 = true := by decide +kernel
theorem s143_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 1 = true := by decide +kernel
theorem s143_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 2 = true := by decide +kernel
theorem k143_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k143_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k143_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s143_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k143_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k143_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k143_3_3_26 k h.1 (by omega)
theorem s143_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 4 = true := by decide +kernel
theorem s143_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 5 = true := by decide +kernel
theorem k143_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k143_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k143_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k143_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k143_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k143_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k143_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k143_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k143_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k143_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k143_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s143_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k143_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k143_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k143_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k143_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k143_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k143_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k143_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k143_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k143_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k143_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k143_3_6_130 k h.1 (by omega)
theorem s143_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 3 7 = true := by decide +kernel
theorem s143_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 0 = true := by decide +kernel
theorem s143_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 1 = true := by decide +kernel
theorem s143_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 2 = true := by decide +kernel
theorem s143_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 3 = true := by decide +kernel
theorem s143_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 4 = true := by decide +kernel
theorem s143_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 5 = true := by decide +kernel
theorem k143_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k143_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k143_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k143_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k143_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k143_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k143_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s143_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k143_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k143_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k143_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k143_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k143_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k143_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k143_4_6_126 k h.1 (by omega)
theorem s143_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 4 7 = true := by decide +kernel
theorem s143_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 0 = true := by decide +kernel
theorem s143_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 1 = true := by decide +kernel
theorem s143_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 2 = true := by decide +kernel
theorem s143_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 3 = true := by decide +kernel
theorem s143_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 4 = true := by decide +kernel
theorem s143_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 5 = true := by decide +kernel
theorem k143_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k143_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k143_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k143_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k143_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k143_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k143_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s143_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k143_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k143_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k143_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k143_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k143_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k143_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 143) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (143 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k143_5_6_126 k h.1 (by omega)
theorem s143_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 5 7 = true := by decide +kernel
theorem s143_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 0 = true := by decide +kernel
theorem s143_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 1 = true := by decide +kernel
theorem s143_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 2 = true := by decide +kernel
theorem s143_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 3 = true := by decide +kernel
theorem s143_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 4 = true := by decide +kernel
theorem s143_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 5 = true := by decide +kernel
theorem s143_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 6 = true := by decide +kernel
theorem k143_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k143_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k143_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k143_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k143_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s143_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k143_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k143_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k143_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k143_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 143) ((InDA1.TCasaD 6 6 7).getD (143 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k143_6_7_12 k h.1 (by omega)
theorem col143_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 7 v) = true := by decide +kernel
theorem col143 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 143) 143 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col143_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col143_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col143_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s143_3_0
    · exact s143_3_1
    · exact s143_3_2
    · exact s143_3_3
    · exact s143_3_4
    · exact s143_3_5
    · exact s143_3_6
    · exact s143_3_7
  · fin_cases v
    · exact s143_4_0
    · exact s143_4_1
    · exact s143_4_2
    · exact s143_4_3
    · exact s143_4_4
    · exact s143_4_5
    · exact s143_4_6
    · exact s143_4_7
  · fin_cases v
    · exact s143_5_0
    · exact s143_5_1
    · exact s143_5_2
    · exact s143_5_3
    · exact s143_5_4
    · exact s143_5_5
    · exact s143_5_6
    · exact s143_5_7
  · fin_cases v
    · exact s143_6_0
    · exact s143_6_1
    · exact s143_6_2
    · exact s143_6_3
    · exact s143_6_4
    · exact s143_6_5
    · exact s143_6_6
    · exact s143_6_7
  · exact List.all_eq_true.mp col143_7 v (List.mem_finRange v)
theorem col144_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 0 v) = true := by decide +kernel
theorem col144_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 1 v) = true := by decide +kernel
theorem col144_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 2 v) = true := by decide +kernel
theorem s144_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 0 = true := by decide +kernel
theorem s144_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 1 = true := by decide +kernel
theorem s144_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 2 = true := by decide +kernel
theorem k144_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k144_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k144_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s144_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k144_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k144_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k144_3_3_26 k h.1 (by omega)
theorem s144_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 4 = true := by decide +kernel
theorem s144_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 5 = true := by decide +kernel
theorem k144_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k144_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k144_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k144_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k144_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k144_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k144_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k144_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k144_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k144_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k144_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s144_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k144_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k144_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k144_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k144_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k144_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k144_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k144_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k144_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k144_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k144_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k144_3_6_130 k h.1 (by omega)
theorem s144_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 3 7 = true := by decide +kernel
theorem s144_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 0 = true := by decide +kernel
theorem s144_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 1 = true := by decide +kernel
theorem s144_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 2 = true := by decide +kernel
theorem s144_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 3 = true := by decide +kernel
theorem s144_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 4 = true := by decide +kernel
theorem s144_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 5 = true := by decide +kernel
theorem k144_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k144_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k144_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k144_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k144_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k144_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k144_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s144_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k144_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k144_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k144_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k144_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k144_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k144_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k144_4_6_126 k h.1 (by omega)
theorem s144_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 4 7 = true := by decide +kernel
theorem s144_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 0 = true := by decide +kernel
theorem s144_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 1 = true := by decide +kernel
theorem s144_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 2 = true := by decide +kernel
theorem s144_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 3 = true := by decide +kernel
theorem s144_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 4 = true := by decide +kernel
theorem s144_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 5 = true := by decide +kernel
theorem k144_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k144_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k144_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k144_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k144_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k144_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k144_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s144_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k144_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k144_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k144_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k144_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k144_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k144_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 144) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (144 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k144_5_6_126 k h.1 (by omega)
theorem s144_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 5 7 = true := by decide +kernel
theorem s144_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 0 = true := by decide +kernel
theorem s144_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 1 = true := by decide +kernel
theorem s144_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 2 = true := by decide +kernel
theorem s144_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 3 = true := by decide +kernel
theorem s144_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 4 = true := by decide +kernel
theorem s144_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 5 = true := by decide +kernel
theorem s144_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 6 = true := by decide +kernel
theorem k144_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k144_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k144_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k144_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k144_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s144_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k144_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k144_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k144_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k144_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 144) ((InDA1.TCasaD 6 6 7).getD (144 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k144_6_7_12 k h.1 (by omega)
theorem col144_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 7 v) = true := by decide +kernel
theorem col144 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 144) 144 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col144_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col144_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col144_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s144_3_0
    · exact s144_3_1
    · exact s144_3_2
    · exact s144_3_3
    · exact s144_3_4
    · exact s144_3_5
    · exact s144_3_6
    · exact s144_3_7
  · fin_cases v
    · exact s144_4_0
    · exact s144_4_1
    · exact s144_4_2
    · exact s144_4_3
    · exact s144_4_4
    · exact s144_4_5
    · exact s144_4_6
    · exact s144_4_7
  · fin_cases v
    · exact s144_5_0
    · exact s144_5_1
    · exact s144_5_2
    · exact s144_5_3
    · exact s144_5_4
    · exact s144_5_5
    · exact s144_5_6
    · exact s144_5_7
  · fin_cases v
    · exact s144_6_0
    · exact s144_6_1
    · exact s144_6_2
    · exact s144_6_3
    · exact s144_6_4
    · exact s144_6_5
    · exact s144_6_6
    · exact s144_6_7
  · exact List.all_eq_true.mp col144_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
