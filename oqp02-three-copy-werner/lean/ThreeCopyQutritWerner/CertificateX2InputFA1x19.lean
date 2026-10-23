module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [95, 100). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col95_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 0 v) = true := by decide +kernel
theorem col95_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 1 v) = true := by decide +kernel
theorem col95_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 2 v) = true := by decide +kernel
theorem s95_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 0 = true := by decide +kernel
theorem s95_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 1 = true := by decide +kernel
theorem s95_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 2 = true := by decide +kernel
theorem k95_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k95_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k95_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s95_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k95_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k95_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k95_3_3_26 k h.1 (by omega)
theorem s95_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 4 = true := by decide +kernel
theorem s95_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 5 = true := by decide +kernel
theorem k95_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k95_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k95_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k95_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k95_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k95_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k95_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k95_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k95_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k95_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k95_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s95_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k95_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k95_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k95_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k95_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k95_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k95_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k95_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k95_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k95_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k95_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k95_3_6_130 k h.1 (by omega)
theorem s95_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 3 7 = true := by decide +kernel
theorem s95_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 0 = true := by decide +kernel
theorem s95_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 1 = true := by decide +kernel
theorem s95_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 2 = true := by decide +kernel
theorem s95_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 3 = true := by decide +kernel
theorem s95_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 4 = true := by decide +kernel
theorem s95_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 5 = true := by decide +kernel
theorem k95_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k95_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k95_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k95_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k95_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k95_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k95_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s95_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k95_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k95_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k95_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k95_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k95_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k95_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k95_4_6_126 k h.1 (by omega)
theorem s95_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 4 7 = true := by decide +kernel
theorem s95_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 0 = true := by decide +kernel
theorem s95_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 1 = true := by decide +kernel
theorem s95_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 2 = true := by decide +kernel
theorem s95_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 3 = true := by decide +kernel
theorem s95_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 4 = true := by decide +kernel
theorem s95_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 5 = true := by decide +kernel
theorem k95_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k95_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k95_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k95_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k95_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k95_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k95_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s95_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k95_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k95_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k95_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k95_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k95_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k95_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 95) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (95 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k95_5_6_126 k h.1 (by omega)
theorem s95_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 5 7 = true := by decide +kernel
theorem s95_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 0 = true := by decide +kernel
theorem s95_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 1 = true := by decide +kernel
theorem s95_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 2 = true := by decide +kernel
theorem s95_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 3 = true := by decide +kernel
theorem s95_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 4 = true := by decide +kernel
theorem s95_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 5 = true := by decide +kernel
theorem s95_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 6 = true := by decide +kernel
theorem k95_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k95_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k95_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k95_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k95_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s95_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k95_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k95_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k95_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k95_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 95) ((InDA1.TCasaD 6 6 7).getD (95 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k95_6_7_12 k h.1 (by omega)
theorem col95_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 7 v) = true := by decide +kernel
theorem col95 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 95) 95 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col95_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col95_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col95_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s95_3_0
    · exact s95_3_1
    · exact s95_3_2
    · exact s95_3_3
    · exact s95_3_4
    · exact s95_3_5
    · exact s95_3_6
    · exact s95_3_7
  · fin_cases v
    · exact s95_4_0
    · exact s95_4_1
    · exact s95_4_2
    · exact s95_4_3
    · exact s95_4_4
    · exact s95_4_5
    · exact s95_4_6
    · exact s95_4_7
  · fin_cases v
    · exact s95_5_0
    · exact s95_5_1
    · exact s95_5_2
    · exact s95_5_3
    · exact s95_5_4
    · exact s95_5_5
    · exact s95_5_6
    · exact s95_5_7
  · fin_cases v
    · exact s95_6_0
    · exact s95_6_1
    · exact s95_6_2
    · exact s95_6_3
    · exact s95_6_4
    · exact s95_6_5
    · exact s95_6_6
    · exact s95_6_7
  · exact List.all_eq_true.mp col95_7 v (List.mem_finRange v)
theorem col96_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 0 v) = true := by decide +kernel
theorem col96_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 1 v) = true := by decide +kernel
theorem col96_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 2 v) = true := by decide +kernel
theorem s96_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 0 = true := by decide +kernel
theorem s96_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 1 = true := by decide +kernel
theorem s96_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 2 = true := by decide +kernel
theorem k96_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k96_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k96_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s96_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k96_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k96_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k96_3_3_26 k h.1 (by omega)
theorem s96_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 4 = true := by decide +kernel
theorem s96_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 5 = true := by decide +kernel
theorem k96_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k96_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k96_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k96_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k96_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k96_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k96_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k96_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k96_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k96_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k96_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s96_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k96_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k96_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k96_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k96_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k96_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k96_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k96_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k96_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k96_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k96_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k96_3_6_130 k h.1 (by omega)
theorem s96_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 3 7 = true := by decide +kernel
theorem s96_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 0 = true := by decide +kernel
theorem s96_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 1 = true := by decide +kernel
theorem s96_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 2 = true := by decide +kernel
theorem s96_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 3 = true := by decide +kernel
theorem s96_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 4 = true := by decide +kernel
theorem s96_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 5 = true := by decide +kernel
theorem k96_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k96_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k96_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k96_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k96_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k96_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k96_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s96_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k96_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k96_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k96_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k96_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k96_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k96_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k96_4_6_126 k h.1 (by omega)
theorem s96_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 4 7 = true := by decide +kernel
theorem s96_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 0 = true := by decide +kernel
theorem s96_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 1 = true := by decide +kernel
theorem s96_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 2 = true := by decide +kernel
theorem s96_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 3 = true := by decide +kernel
theorem s96_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 4 = true := by decide +kernel
theorem s96_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 5 = true := by decide +kernel
theorem k96_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k96_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k96_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k96_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k96_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k96_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k96_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s96_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k96_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k96_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k96_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k96_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k96_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k96_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 96) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (96 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k96_5_6_126 k h.1 (by omega)
theorem s96_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 5 7 = true := by decide +kernel
theorem s96_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 0 = true := by decide +kernel
theorem s96_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 1 = true := by decide +kernel
theorem s96_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 2 = true := by decide +kernel
theorem s96_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 3 = true := by decide +kernel
theorem s96_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 4 = true := by decide +kernel
theorem s96_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 5 = true := by decide +kernel
theorem s96_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 6 = true := by decide +kernel
theorem k96_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k96_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k96_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k96_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k96_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s96_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k96_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k96_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k96_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k96_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 96) ((InDA1.TCasaD 6 6 7).getD (96 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k96_6_7_12 k h.1 (by omega)
theorem col96_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 7 v) = true := by decide +kernel
theorem col96 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 96) 96 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col96_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col96_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col96_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s96_3_0
    · exact s96_3_1
    · exact s96_3_2
    · exact s96_3_3
    · exact s96_3_4
    · exact s96_3_5
    · exact s96_3_6
    · exact s96_3_7
  · fin_cases v
    · exact s96_4_0
    · exact s96_4_1
    · exact s96_4_2
    · exact s96_4_3
    · exact s96_4_4
    · exact s96_4_5
    · exact s96_4_6
    · exact s96_4_7
  · fin_cases v
    · exact s96_5_0
    · exact s96_5_1
    · exact s96_5_2
    · exact s96_5_3
    · exact s96_5_4
    · exact s96_5_5
    · exact s96_5_6
    · exact s96_5_7
  · fin_cases v
    · exact s96_6_0
    · exact s96_6_1
    · exact s96_6_2
    · exact s96_6_3
    · exact s96_6_4
    · exact s96_6_5
    · exact s96_6_6
    · exact s96_6_7
  · exact List.all_eq_true.mp col96_7 v (List.mem_finRange v)
theorem col97_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 0 v) = true := by decide +kernel
theorem col97_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 1 v) = true := by decide +kernel
theorem col97_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 2 v) = true := by decide +kernel
theorem s97_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 0 = true := by decide +kernel
theorem s97_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 1 = true := by decide +kernel
theorem s97_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 2 = true := by decide +kernel
theorem k97_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k97_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k97_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s97_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k97_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k97_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k97_3_3_26 k h.1 (by omega)
theorem s97_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 4 = true := by decide +kernel
theorem s97_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 5 = true := by decide +kernel
theorem k97_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k97_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k97_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k97_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k97_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k97_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k97_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k97_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k97_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k97_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k97_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s97_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k97_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k97_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k97_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k97_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k97_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k97_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k97_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k97_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k97_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k97_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k97_3_6_130 k h.1 (by omega)
theorem s97_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 3 7 = true := by decide +kernel
theorem s97_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 0 = true := by decide +kernel
theorem s97_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 1 = true := by decide +kernel
theorem s97_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 2 = true := by decide +kernel
theorem s97_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 3 = true := by decide +kernel
theorem s97_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 4 = true := by decide +kernel
theorem s97_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 5 = true := by decide +kernel
theorem k97_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k97_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k97_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k97_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k97_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k97_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k97_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s97_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k97_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k97_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k97_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k97_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k97_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k97_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k97_4_6_126 k h.1 (by omega)
theorem s97_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 4 7 = true := by decide +kernel
theorem s97_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 0 = true := by decide +kernel
theorem s97_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 1 = true := by decide +kernel
theorem s97_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 2 = true := by decide +kernel
theorem s97_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 3 = true := by decide +kernel
theorem s97_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 4 = true := by decide +kernel
theorem s97_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 5 = true := by decide +kernel
theorem k97_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k97_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k97_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k97_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k97_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k97_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k97_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s97_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k97_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k97_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k97_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k97_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k97_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k97_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 97) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (97 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k97_5_6_126 k h.1 (by omega)
theorem s97_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 5 7 = true := by decide +kernel
theorem s97_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 0 = true := by decide +kernel
theorem s97_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 1 = true := by decide +kernel
theorem s97_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 2 = true := by decide +kernel
theorem s97_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 3 = true := by decide +kernel
theorem s97_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 4 = true := by decide +kernel
theorem s97_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 5 = true := by decide +kernel
theorem s97_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 6 = true := by decide +kernel
theorem k97_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k97_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k97_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k97_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k97_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s97_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k97_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k97_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k97_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k97_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 97) ((InDA1.TCasaD 6 6 7).getD (97 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k97_6_7_12 k h.1 (by omega)
theorem col97_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 7 v) = true := by decide +kernel
theorem col97 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 97) 97 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col97_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col97_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col97_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s97_3_0
    · exact s97_3_1
    · exact s97_3_2
    · exact s97_3_3
    · exact s97_3_4
    · exact s97_3_5
    · exact s97_3_6
    · exact s97_3_7
  · fin_cases v
    · exact s97_4_0
    · exact s97_4_1
    · exact s97_4_2
    · exact s97_4_3
    · exact s97_4_4
    · exact s97_4_5
    · exact s97_4_6
    · exact s97_4_7
  · fin_cases v
    · exact s97_5_0
    · exact s97_5_1
    · exact s97_5_2
    · exact s97_5_3
    · exact s97_5_4
    · exact s97_5_5
    · exact s97_5_6
    · exact s97_5_7
  · fin_cases v
    · exact s97_6_0
    · exact s97_6_1
    · exact s97_6_2
    · exact s97_6_3
    · exact s97_6_4
    · exact s97_6_5
    · exact s97_6_6
    · exact s97_6_7
  · exact List.all_eq_true.mp col97_7 v (List.mem_finRange v)
theorem col98_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 0 v) = true := by decide +kernel
theorem col98_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 1 v) = true := by decide +kernel
theorem col98_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 2 v) = true := by decide +kernel
theorem s98_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 0 = true := by decide +kernel
theorem s98_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 1 = true := by decide +kernel
theorem s98_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 2 = true := by decide +kernel
theorem k98_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k98_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k98_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s98_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k98_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k98_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k98_3_3_26 k h.1 (by omega)
theorem s98_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 4 = true := by decide +kernel
theorem s98_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 5 = true := by decide +kernel
theorem k98_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k98_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k98_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k98_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k98_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k98_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k98_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k98_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k98_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k98_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k98_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s98_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k98_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k98_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k98_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k98_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k98_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k98_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k98_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k98_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k98_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k98_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k98_3_6_130 k h.1 (by omega)
theorem s98_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 3 7 = true := by decide +kernel
theorem s98_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 0 = true := by decide +kernel
theorem s98_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 1 = true := by decide +kernel
theorem s98_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 2 = true := by decide +kernel
theorem s98_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 3 = true := by decide +kernel
theorem s98_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 4 = true := by decide +kernel
theorem s98_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 5 = true := by decide +kernel
theorem k98_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k98_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k98_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k98_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k98_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k98_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k98_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s98_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k98_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k98_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k98_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k98_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k98_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k98_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k98_4_6_126 k h.1 (by omega)
theorem s98_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 4 7 = true := by decide +kernel
theorem s98_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 0 = true := by decide +kernel
theorem s98_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 1 = true := by decide +kernel
theorem s98_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 2 = true := by decide +kernel
theorem s98_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 3 = true := by decide +kernel
theorem s98_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 4 = true := by decide +kernel
theorem s98_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 5 = true := by decide +kernel
theorem k98_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k98_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k98_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k98_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k98_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k98_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k98_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s98_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k98_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k98_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k98_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k98_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k98_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k98_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 98) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (98 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k98_5_6_126 k h.1 (by omega)
theorem s98_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 5 7 = true := by decide +kernel
theorem s98_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 0 = true := by decide +kernel
theorem s98_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 1 = true := by decide +kernel
theorem s98_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 2 = true := by decide +kernel
theorem s98_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 3 = true := by decide +kernel
theorem s98_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 4 = true := by decide +kernel
theorem s98_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 5 = true := by decide +kernel
theorem s98_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 6 = true := by decide +kernel
theorem k98_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k98_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k98_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k98_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k98_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s98_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k98_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k98_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k98_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k98_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 98) ((InDA1.TCasaD 6 6 7).getD (98 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k98_6_7_12 k h.1 (by omega)
theorem col98_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 7 v) = true := by decide +kernel
theorem col98 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 98) 98 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col98_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col98_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col98_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s98_3_0
    · exact s98_3_1
    · exact s98_3_2
    · exact s98_3_3
    · exact s98_3_4
    · exact s98_3_5
    · exact s98_3_6
    · exact s98_3_7
  · fin_cases v
    · exact s98_4_0
    · exact s98_4_1
    · exact s98_4_2
    · exact s98_4_3
    · exact s98_4_4
    · exact s98_4_5
    · exact s98_4_6
    · exact s98_4_7
  · fin_cases v
    · exact s98_5_0
    · exact s98_5_1
    · exact s98_5_2
    · exact s98_5_3
    · exact s98_5_4
    · exact s98_5_5
    · exact s98_5_6
    · exact s98_5_7
  · fin_cases v
    · exact s98_6_0
    · exact s98_6_1
    · exact s98_6_2
    · exact s98_6_3
    · exact s98_6_4
    · exact s98_6_5
    · exact s98_6_6
    · exact s98_6_7
  · exact List.all_eq_true.mp col98_7 v (List.mem_finRange v)
theorem col99_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 0 v) = true := by decide +kernel
theorem col99_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 1 v) = true := by decide +kernel
theorem col99_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 2 v) = true := by decide +kernel
theorem s99_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 0 = true := by decide +kernel
theorem s99_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 1 = true := by decide +kernel
theorem s99_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 2 = true := by decide +kernel
theorem k99_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k99_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k99_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s99_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k99_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k99_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k99_3_3_26 k h.1 (by omega)
theorem s99_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 4 = true := by decide +kernel
theorem s99_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 5 = true := by decide +kernel
theorem k99_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k99_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k99_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k99_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k99_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k99_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k99_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k99_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k99_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k99_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k99_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s99_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k99_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k99_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k99_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k99_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k99_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k99_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k99_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k99_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k99_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k99_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k99_3_6_130 k h.1 (by omega)
theorem s99_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 3 7 = true := by decide +kernel
theorem s99_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 0 = true := by decide +kernel
theorem s99_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 1 = true := by decide +kernel
theorem s99_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 2 = true := by decide +kernel
theorem s99_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 3 = true := by decide +kernel
theorem s99_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 4 = true := by decide +kernel
theorem s99_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 5 = true := by decide +kernel
theorem k99_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k99_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k99_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k99_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k99_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k99_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k99_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s99_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k99_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k99_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k99_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k99_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k99_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k99_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k99_4_6_126 k h.1 (by omega)
theorem s99_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 4 7 = true := by decide +kernel
theorem s99_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 0 = true := by decide +kernel
theorem s99_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 1 = true := by decide +kernel
theorem s99_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 2 = true := by decide +kernel
theorem s99_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 3 = true := by decide +kernel
theorem s99_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 4 = true := by decide +kernel
theorem s99_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 5 = true := by decide +kernel
theorem k99_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k99_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k99_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k99_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k99_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k99_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k99_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s99_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k99_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k99_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k99_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k99_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k99_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k99_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 99) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (99 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k99_5_6_126 k h.1 (by omega)
theorem s99_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 5 7 = true := by decide +kernel
theorem s99_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 0 = true := by decide +kernel
theorem s99_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 1 = true := by decide +kernel
theorem s99_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 2 = true := by decide +kernel
theorem s99_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 3 = true := by decide +kernel
theorem s99_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 4 = true := by decide +kernel
theorem s99_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 5 = true := by decide +kernel
theorem s99_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 6 = true := by decide +kernel
theorem k99_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k99_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k99_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k99_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k99_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s99_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k99_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k99_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k99_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k99_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 99) ((InDA1.TCasaD 6 6 7).getD (99 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k99_6_7_12 k h.1 (by omega)
theorem col99_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 7 v) = true := by decide +kernel
theorem col99 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 99) 99 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col99_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col99_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col99_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s99_3_0
    · exact s99_3_1
    · exact s99_3_2
    · exact s99_3_3
    · exact s99_3_4
    · exact s99_3_5
    · exact s99_3_6
    · exact s99_3_7
  · fin_cases v
    · exact s99_4_0
    · exact s99_4_1
    · exact s99_4_2
    · exact s99_4_3
    · exact s99_4_4
    · exact s99_4_5
    · exact s99_4_6
    · exact s99_4_7
  · fin_cases v
    · exact s99_5_0
    · exact s99_5_1
    · exact s99_5_2
    · exact s99_5_3
    · exact s99_5_4
    · exact s99_5_5
    · exact s99_5_6
    · exact s99_5_7
  · fin_cases v
    · exact s99_6_0
    · exact s99_6_1
    · exact s99_6_2
    · exact s99_6_3
    · exact s99_6_4
    · exact s99_6_5
    · exact s99_6_6
    · exact s99_6_7
  · exact List.all_eq_true.mp col99_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
