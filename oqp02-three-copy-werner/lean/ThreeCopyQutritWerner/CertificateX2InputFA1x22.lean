module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [110, 115). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col110_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 0 v) = true := by decide +kernel
theorem col110_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 1 v) = true := by decide +kernel
theorem col110_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 2 v) = true := by decide +kernel
theorem s110_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 0 = true := by decide +kernel
theorem s110_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 1 = true := by decide +kernel
theorem s110_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 2 = true := by decide +kernel
theorem k110_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k110_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k110_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s110_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k110_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k110_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k110_3_3_26 k h.1 (by omega)
theorem s110_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 4 = true := by decide +kernel
theorem s110_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 5 = true := by decide +kernel
theorem k110_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k110_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k110_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k110_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k110_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k110_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k110_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k110_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k110_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k110_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k110_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s110_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k110_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k110_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k110_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k110_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k110_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k110_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k110_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k110_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k110_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k110_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k110_3_6_130 k h.1 (by omega)
theorem s110_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 3 7 = true := by decide +kernel
theorem s110_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 0 = true := by decide +kernel
theorem s110_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 1 = true := by decide +kernel
theorem s110_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 2 = true := by decide +kernel
theorem s110_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 3 = true := by decide +kernel
theorem s110_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 4 = true := by decide +kernel
theorem s110_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 5 = true := by decide +kernel
theorem k110_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k110_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k110_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k110_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k110_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k110_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k110_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s110_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k110_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k110_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k110_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k110_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k110_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k110_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k110_4_6_126 k h.1 (by omega)
theorem s110_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 4 7 = true := by decide +kernel
theorem s110_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 0 = true := by decide +kernel
theorem s110_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 1 = true := by decide +kernel
theorem s110_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 2 = true := by decide +kernel
theorem s110_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 3 = true := by decide +kernel
theorem s110_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 4 = true := by decide +kernel
theorem s110_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 5 = true := by decide +kernel
theorem k110_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k110_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k110_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k110_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k110_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k110_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k110_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s110_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k110_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k110_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k110_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k110_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k110_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k110_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 110) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (110 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k110_5_6_126 k h.1 (by omega)
theorem s110_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 5 7 = true := by decide +kernel
theorem s110_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 0 = true := by decide +kernel
theorem s110_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 1 = true := by decide +kernel
theorem s110_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 2 = true := by decide +kernel
theorem s110_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 3 = true := by decide +kernel
theorem s110_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 4 = true := by decide +kernel
theorem s110_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 5 = true := by decide +kernel
theorem s110_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 6 = true := by decide +kernel
theorem k110_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k110_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k110_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k110_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k110_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s110_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k110_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k110_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k110_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k110_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 110) ((InDA1.TCasaD 6 6 7).getD (110 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k110_6_7_12 k h.1 (by omega)
theorem col110_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 7 v) = true := by decide +kernel
theorem col110 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 110) 110 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col110_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col110_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col110_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s110_3_0
    · exact s110_3_1
    · exact s110_3_2
    · exact s110_3_3
    · exact s110_3_4
    · exact s110_3_5
    · exact s110_3_6
    · exact s110_3_7
  · fin_cases v
    · exact s110_4_0
    · exact s110_4_1
    · exact s110_4_2
    · exact s110_4_3
    · exact s110_4_4
    · exact s110_4_5
    · exact s110_4_6
    · exact s110_4_7
  · fin_cases v
    · exact s110_5_0
    · exact s110_5_1
    · exact s110_5_2
    · exact s110_5_3
    · exact s110_5_4
    · exact s110_5_5
    · exact s110_5_6
    · exact s110_5_7
  · fin_cases v
    · exact s110_6_0
    · exact s110_6_1
    · exact s110_6_2
    · exact s110_6_3
    · exact s110_6_4
    · exact s110_6_5
    · exact s110_6_6
    · exact s110_6_7
  · exact List.all_eq_true.mp col110_7 v (List.mem_finRange v)
theorem col111_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 0 v) = true := by decide +kernel
theorem col111_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 1 v) = true := by decide +kernel
theorem col111_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 2 v) = true := by decide +kernel
theorem s111_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 0 = true := by decide +kernel
theorem s111_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 1 = true := by decide +kernel
theorem s111_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 2 = true := by decide +kernel
theorem k111_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k111_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k111_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s111_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k111_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k111_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k111_3_3_26 k h.1 (by omega)
theorem s111_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 4 = true := by decide +kernel
theorem s111_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 5 = true := by decide +kernel
theorem k111_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k111_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k111_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k111_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k111_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k111_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k111_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k111_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k111_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k111_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k111_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s111_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k111_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k111_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k111_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k111_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k111_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k111_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k111_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k111_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k111_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k111_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k111_3_6_130 k h.1 (by omega)
theorem s111_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 3 7 = true := by decide +kernel
theorem s111_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 0 = true := by decide +kernel
theorem s111_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 1 = true := by decide +kernel
theorem s111_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 2 = true := by decide +kernel
theorem s111_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 3 = true := by decide +kernel
theorem s111_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 4 = true := by decide +kernel
theorem s111_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 5 = true := by decide +kernel
theorem k111_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k111_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k111_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k111_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k111_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k111_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k111_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s111_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k111_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k111_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k111_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k111_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k111_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k111_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k111_4_6_126 k h.1 (by omega)
theorem s111_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 4 7 = true := by decide +kernel
theorem s111_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 0 = true := by decide +kernel
theorem s111_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 1 = true := by decide +kernel
theorem s111_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 2 = true := by decide +kernel
theorem s111_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 3 = true := by decide +kernel
theorem s111_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 4 = true := by decide +kernel
theorem s111_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 5 = true := by decide +kernel
theorem k111_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k111_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k111_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k111_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k111_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k111_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k111_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s111_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k111_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k111_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k111_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k111_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k111_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k111_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 111) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (111 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k111_5_6_126 k h.1 (by omega)
theorem s111_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 5 7 = true := by decide +kernel
theorem s111_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 0 = true := by decide +kernel
theorem s111_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 1 = true := by decide +kernel
theorem s111_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 2 = true := by decide +kernel
theorem s111_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 3 = true := by decide +kernel
theorem s111_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 4 = true := by decide +kernel
theorem s111_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 5 = true := by decide +kernel
theorem s111_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 6 = true := by decide +kernel
theorem k111_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k111_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k111_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k111_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k111_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s111_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k111_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k111_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k111_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k111_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 111) ((InDA1.TCasaD 6 6 7).getD (111 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k111_6_7_12 k h.1 (by omega)
theorem col111_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 7 v) = true := by decide +kernel
theorem col111 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 111) 111 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col111_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col111_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col111_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s111_3_0
    · exact s111_3_1
    · exact s111_3_2
    · exact s111_3_3
    · exact s111_3_4
    · exact s111_3_5
    · exact s111_3_6
    · exact s111_3_7
  · fin_cases v
    · exact s111_4_0
    · exact s111_4_1
    · exact s111_4_2
    · exact s111_4_3
    · exact s111_4_4
    · exact s111_4_5
    · exact s111_4_6
    · exact s111_4_7
  · fin_cases v
    · exact s111_5_0
    · exact s111_5_1
    · exact s111_5_2
    · exact s111_5_3
    · exact s111_5_4
    · exact s111_5_5
    · exact s111_5_6
    · exact s111_5_7
  · fin_cases v
    · exact s111_6_0
    · exact s111_6_1
    · exact s111_6_2
    · exact s111_6_3
    · exact s111_6_4
    · exact s111_6_5
    · exact s111_6_6
    · exact s111_6_7
  · exact List.all_eq_true.mp col111_7 v (List.mem_finRange v)
theorem col112_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 0 v) = true := by decide +kernel
theorem col112_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 1 v) = true := by decide +kernel
theorem col112_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 2 v) = true := by decide +kernel
theorem s112_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 0 = true := by decide +kernel
theorem s112_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 1 = true := by decide +kernel
theorem s112_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 2 = true := by decide +kernel
theorem k112_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k112_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k112_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s112_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k112_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k112_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k112_3_3_26 k h.1 (by omega)
theorem s112_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 4 = true := by decide +kernel
theorem s112_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 5 = true := by decide +kernel
theorem k112_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k112_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k112_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k112_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k112_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k112_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k112_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k112_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k112_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k112_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k112_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s112_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k112_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k112_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k112_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k112_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k112_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k112_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k112_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k112_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k112_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k112_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k112_3_6_130 k h.1 (by omega)
theorem s112_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 3 7 = true := by decide +kernel
theorem s112_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 0 = true := by decide +kernel
theorem s112_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 1 = true := by decide +kernel
theorem s112_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 2 = true := by decide +kernel
theorem s112_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 3 = true := by decide +kernel
theorem s112_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 4 = true := by decide +kernel
theorem s112_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 5 = true := by decide +kernel
theorem k112_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k112_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k112_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k112_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k112_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k112_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k112_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s112_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k112_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k112_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k112_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k112_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k112_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k112_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k112_4_6_126 k h.1 (by omega)
theorem s112_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 4 7 = true := by decide +kernel
theorem s112_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 0 = true := by decide +kernel
theorem s112_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 1 = true := by decide +kernel
theorem s112_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 2 = true := by decide +kernel
theorem s112_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 3 = true := by decide +kernel
theorem s112_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 4 = true := by decide +kernel
theorem s112_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 5 = true := by decide +kernel
theorem k112_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k112_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k112_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k112_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k112_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k112_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k112_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s112_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k112_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k112_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k112_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k112_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k112_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k112_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 112) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (112 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k112_5_6_126 k h.1 (by omega)
theorem s112_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 5 7 = true := by decide +kernel
theorem s112_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 0 = true := by decide +kernel
theorem s112_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 1 = true := by decide +kernel
theorem s112_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 2 = true := by decide +kernel
theorem s112_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 3 = true := by decide +kernel
theorem s112_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 4 = true := by decide +kernel
theorem s112_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 5 = true := by decide +kernel
theorem s112_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 6 = true := by decide +kernel
theorem k112_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k112_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k112_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k112_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k112_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s112_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k112_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k112_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k112_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k112_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 112) ((InDA1.TCasaD 6 6 7).getD (112 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k112_6_7_12 k h.1 (by omega)
theorem col112_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 7 v) = true := by decide +kernel
theorem col112 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 112) 112 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col112_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col112_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col112_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s112_3_0
    · exact s112_3_1
    · exact s112_3_2
    · exact s112_3_3
    · exact s112_3_4
    · exact s112_3_5
    · exact s112_3_6
    · exact s112_3_7
  · fin_cases v
    · exact s112_4_0
    · exact s112_4_1
    · exact s112_4_2
    · exact s112_4_3
    · exact s112_4_4
    · exact s112_4_5
    · exact s112_4_6
    · exact s112_4_7
  · fin_cases v
    · exact s112_5_0
    · exact s112_5_1
    · exact s112_5_2
    · exact s112_5_3
    · exact s112_5_4
    · exact s112_5_5
    · exact s112_5_6
    · exact s112_5_7
  · fin_cases v
    · exact s112_6_0
    · exact s112_6_1
    · exact s112_6_2
    · exact s112_6_3
    · exact s112_6_4
    · exact s112_6_5
    · exact s112_6_6
    · exact s112_6_7
  · exact List.all_eq_true.mp col112_7 v (List.mem_finRange v)
theorem col113_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 0 v) = true := by decide +kernel
theorem col113_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 1 v) = true := by decide +kernel
theorem col113_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 2 v) = true := by decide +kernel
theorem s113_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 0 = true := by decide +kernel
theorem s113_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 1 = true := by decide +kernel
theorem s113_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 2 = true := by decide +kernel
theorem k113_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k113_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k113_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s113_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k113_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k113_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k113_3_3_26 k h.1 (by omega)
theorem s113_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 4 = true := by decide +kernel
theorem s113_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 5 = true := by decide +kernel
theorem k113_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k113_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k113_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k113_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k113_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k113_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k113_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k113_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k113_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k113_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k113_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s113_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k113_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k113_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k113_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k113_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k113_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k113_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k113_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k113_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k113_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k113_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k113_3_6_130 k h.1 (by omega)
theorem s113_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 3 7 = true := by decide +kernel
theorem s113_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 0 = true := by decide +kernel
theorem s113_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 1 = true := by decide +kernel
theorem s113_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 2 = true := by decide +kernel
theorem s113_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 3 = true := by decide +kernel
theorem s113_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 4 = true := by decide +kernel
theorem s113_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 5 = true := by decide +kernel
theorem k113_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k113_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k113_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k113_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k113_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k113_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k113_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s113_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k113_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k113_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k113_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k113_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k113_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k113_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k113_4_6_126 k h.1 (by omega)
theorem s113_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 4 7 = true := by decide +kernel
theorem s113_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 0 = true := by decide +kernel
theorem s113_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 1 = true := by decide +kernel
theorem s113_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 2 = true := by decide +kernel
theorem s113_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 3 = true := by decide +kernel
theorem s113_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 4 = true := by decide +kernel
theorem s113_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 5 = true := by decide +kernel
theorem k113_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k113_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k113_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k113_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k113_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k113_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k113_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s113_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k113_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k113_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k113_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k113_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k113_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k113_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 113) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (113 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k113_5_6_126 k h.1 (by omega)
theorem s113_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 5 7 = true := by decide +kernel
theorem s113_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 0 = true := by decide +kernel
theorem s113_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 1 = true := by decide +kernel
theorem s113_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 2 = true := by decide +kernel
theorem s113_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 3 = true := by decide +kernel
theorem s113_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 4 = true := by decide +kernel
theorem s113_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 5 = true := by decide +kernel
theorem s113_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 6 = true := by decide +kernel
theorem k113_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k113_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k113_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k113_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k113_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s113_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k113_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k113_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k113_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k113_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 113) ((InDA1.TCasaD 6 6 7).getD (113 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k113_6_7_12 k h.1 (by omega)
theorem col113_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 7 v) = true := by decide +kernel
theorem col113 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 113) 113 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col113_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col113_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col113_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s113_3_0
    · exact s113_3_1
    · exact s113_3_2
    · exact s113_3_3
    · exact s113_3_4
    · exact s113_3_5
    · exact s113_3_6
    · exact s113_3_7
  · fin_cases v
    · exact s113_4_0
    · exact s113_4_1
    · exact s113_4_2
    · exact s113_4_3
    · exact s113_4_4
    · exact s113_4_5
    · exact s113_4_6
    · exact s113_4_7
  · fin_cases v
    · exact s113_5_0
    · exact s113_5_1
    · exact s113_5_2
    · exact s113_5_3
    · exact s113_5_4
    · exact s113_5_5
    · exact s113_5_6
    · exact s113_5_7
  · fin_cases v
    · exact s113_6_0
    · exact s113_6_1
    · exact s113_6_2
    · exact s113_6_3
    · exact s113_6_4
    · exact s113_6_5
    · exact s113_6_6
    · exact s113_6_7
  · exact List.all_eq_true.mp col113_7 v (List.mem_finRange v)
theorem col114_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 0 v) = true := by decide +kernel
theorem col114_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 1 v) = true := by decide +kernel
theorem col114_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 2 v) = true := by decide +kernel
theorem s114_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 0 = true := by decide +kernel
theorem s114_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 1 = true := by decide +kernel
theorem s114_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 2 = true := by decide +kernel
theorem k114_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k114_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k114_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s114_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k114_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k114_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k114_3_3_26 k h.1 (by omega)
theorem s114_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 4 = true := by decide +kernel
theorem s114_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 5 = true := by decide +kernel
theorem k114_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k114_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k114_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k114_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k114_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k114_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k114_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k114_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k114_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k114_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k114_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s114_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k114_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k114_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k114_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k114_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k114_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k114_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k114_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k114_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k114_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k114_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k114_3_6_130 k h.1 (by omega)
theorem s114_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 3 7 = true := by decide +kernel
theorem s114_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 0 = true := by decide +kernel
theorem s114_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 1 = true := by decide +kernel
theorem s114_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 2 = true := by decide +kernel
theorem s114_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 3 = true := by decide +kernel
theorem s114_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 4 = true := by decide +kernel
theorem s114_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 5 = true := by decide +kernel
theorem k114_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k114_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k114_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k114_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k114_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k114_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k114_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s114_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k114_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k114_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k114_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k114_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k114_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k114_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k114_4_6_126 k h.1 (by omega)
theorem s114_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 4 7 = true := by decide +kernel
theorem s114_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 0 = true := by decide +kernel
theorem s114_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 1 = true := by decide +kernel
theorem s114_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 2 = true := by decide +kernel
theorem s114_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 3 = true := by decide +kernel
theorem s114_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 4 = true := by decide +kernel
theorem s114_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 5 = true := by decide +kernel
theorem k114_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k114_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k114_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k114_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k114_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k114_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k114_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s114_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k114_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k114_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k114_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k114_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k114_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k114_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 114) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (114 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k114_5_6_126 k h.1 (by omega)
theorem s114_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 5 7 = true := by decide +kernel
theorem s114_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 0 = true := by decide +kernel
theorem s114_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 1 = true := by decide +kernel
theorem s114_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 2 = true := by decide +kernel
theorem s114_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 3 = true := by decide +kernel
theorem s114_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 4 = true := by decide +kernel
theorem s114_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 5 = true := by decide +kernel
theorem s114_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 6 = true := by decide +kernel
theorem k114_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k114_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k114_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k114_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k114_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s114_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k114_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k114_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k114_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k114_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 114) ((InDA1.TCasaD 6 6 7).getD (114 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k114_6_7_12 k h.1 (by omega)
theorem col114_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 7 v) = true := by decide +kernel
theorem col114 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 114) 114 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col114_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col114_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col114_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s114_3_0
    · exact s114_3_1
    · exact s114_3_2
    · exact s114_3_3
    · exact s114_3_4
    · exact s114_3_5
    · exact s114_3_6
    · exact s114_3_7
  · fin_cases v
    · exact s114_4_0
    · exact s114_4_1
    · exact s114_4_2
    · exact s114_4_3
    · exact s114_4_4
    · exact s114_4_5
    · exact s114_4_6
    · exact s114_4_7
  · fin_cases v
    · exact s114_5_0
    · exact s114_5_1
    · exact s114_5_2
    · exact s114_5_3
    · exact s114_5_4
    · exact s114_5_5
    · exact s114_5_6
    · exact s114_5_7
  · fin_cases v
    · exact s114_6_0
    · exact s114_6_1
    · exact s114_6_2
    · exact s114_6_3
    · exact s114_6_4
    · exact s114_6_5
    · exact s114_6_6
    · exact s114_6_7
  · exact List.all_eq_true.mp col114_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
