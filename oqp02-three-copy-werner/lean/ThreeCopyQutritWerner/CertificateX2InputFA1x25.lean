module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [125, 130). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col125_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 0 v) = true := by decide +kernel
theorem col125_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 1 v) = true := by decide +kernel
theorem col125_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 2 v) = true := by decide +kernel
theorem s125_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 0 = true := by decide +kernel
theorem s125_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 1 = true := by decide +kernel
theorem s125_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 2 = true := by decide +kernel
theorem k125_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k125_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k125_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s125_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k125_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k125_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k125_3_3_26 k h.1 (by omega)
theorem s125_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 4 = true := by decide +kernel
theorem s125_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 5 = true := by decide +kernel
theorem k125_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k125_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k125_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k125_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k125_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k125_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k125_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k125_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k125_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k125_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k125_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s125_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k125_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k125_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k125_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k125_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k125_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k125_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k125_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k125_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k125_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k125_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k125_3_6_130 k h.1 (by omega)
theorem s125_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 3 7 = true := by decide +kernel
theorem s125_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 0 = true := by decide +kernel
theorem s125_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 1 = true := by decide +kernel
theorem s125_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 2 = true := by decide +kernel
theorem s125_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 3 = true := by decide +kernel
theorem s125_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 4 = true := by decide +kernel
theorem s125_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 5 = true := by decide +kernel
theorem k125_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k125_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k125_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k125_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k125_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k125_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k125_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s125_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k125_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k125_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k125_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k125_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k125_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k125_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k125_4_6_126 k h.1 (by omega)
theorem s125_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 4 7 = true := by decide +kernel
theorem s125_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 0 = true := by decide +kernel
theorem s125_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 1 = true := by decide +kernel
theorem s125_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 2 = true := by decide +kernel
theorem s125_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 3 = true := by decide +kernel
theorem s125_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 4 = true := by decide +kernel
theorem s125_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 5 = true := by decide +kernel
theorem k125_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k125_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k125_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k125_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k125_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k125_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k125_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s125_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k125_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k125_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k125_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k125_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k125_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k125_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 125) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (125 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k125_5_6_126 k h.1 (by omega)
theorem s125_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 5 7 = true := by decide +kernel
theorem s125_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 0 = true := by decide +kernel
theorem s125_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 1 = true := by decide +kernel
theorem s125_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 2 = true := by decide +kernel
theorem s125_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 3 = true := by decide +kernel
theorem s125_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 4 = true := by decide +kernel
theorem s125_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 5 = true := by decide +kernel
theorem s125_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 6 = true := by decide +kernel
theorem k125_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k125_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k125_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k125_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k125_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s125_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k125_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k125_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k125_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k125_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 125) ((InDA1.TCasaD 6 6 7).getD (125 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k125_6_7_12 k h.1 (by omega)
theorem col125_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 7 v) = true := by decide +kernel
theorem col125 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 125) 125 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col125_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col125_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col125_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s125_3_0
    · exact s125_3_1
    · exact s125_3_2
    · exact s125_3_3
    · exact s125_3_4
    · exact s125_3_5
    · exact s125_3_6
    · exact s125_3_7
  · fin_cases v
    · exact s125_4_0
    · exact s125_4_1
    · exact s125_4_2
    · exact s125_4_3
    · exact s125_4_4
    · exact s125_4_5
    · exact s125_4_6
    · exact s125_4_7
  · fin_cases v
    · exact s125_5_0
    · exact s125_5_1
    · exact s125_5_2
    · exact s125_5_3
    · exact s125_5_4
    · exact s125_5_5
    · exact s125_5_6
    · exact s125_5_7
  · fin_cases v
    · exact s125_6_0
    · exact s125_6_1
    · exact s125_6_2
    · exact s125_6_3
    · exact s125_6_4
    · exact s125_6_5
    · exact s125_6_6
    · exact s125_6_7
  · exact List.all_eq_true.mp col125_7 v (List.mem_finRange v)
theorem col126_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 0 v) = true := by decide +kernel
theorem col126_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 1 v) = true := by decide +kernel
theorem col126_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 2 v) = true := by decide +kernel
theorem s126_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 0 = true := by decide +kernel
theorem s126_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 1 = true := by decide +kernel
theorem s126_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 2 = true := by decide +kernel
theorem k126_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k126_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k126_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s126_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k126_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k126_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k126_3_3_26 k h.1 (by omega)
theorem s126_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 4 = true := by decide +kernel
theorem s126_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 5 = true := by decide +kernel
theorem k126_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k126_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k126_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k126_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k126_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k126_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k126_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k126_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k126_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k126_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k126_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s126_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k126_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k126_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k126_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k126_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k126_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k126_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k126_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k126_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k126_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k126_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k126_3_6_130 k h.1 (by omega)
theorem s126_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 3 7 = true := by decide +kernel
theorem s126_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 0 = true := by decide +kernel
theorem s126_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 1 = true := by decide +kernel
theorem s126_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 2 = true := by decide +kernel
theorem s126_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 3 = true := by decide +kernel
theorem s126_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 4 = true := by decide +kernel
theorem s126_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 5 = true := by decide +kernel
theorem k126_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k126_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k126_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k126_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k126_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k126_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k126_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s126_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k126_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k126_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k126_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k126_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k126_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k126_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k126_4_6_126 k h.1 (by omega)
theorem s126_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 4 7 = true := by decide +kernel
theorem s126_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 0 = true := by decide +kernel
theorem s126_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 1 = true := by decide +kernel
theorem s126_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 2 = true := by decide +kernel
theorem s126_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 3 = true := by decide +kernel
theorem s126_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 4 = true := by decide +kernel
theorem s126_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 5 = true := by decide +kernel
theorem k126_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k126_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k126_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k126_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k126_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k126_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k126_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s126_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k126_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k126_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k126_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k126_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k126_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k126_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 126) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (126 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k126_5_6_126 k h.1 (by omega)
theorem s126_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 5 7 = true := by decide +kernel
theorem s126_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 0 = true := by decide +kernel
theorem s126_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 1 = true := by decide +kernel
theorem s126_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 2 = true := by decide +kernel
theorem s126_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 3 = true := by decide +kernel
theorem s126_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 4 = true := by decide +kernel
theorem s126_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 5 = true := by decide +kernel
theorem s126_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 6 = true := by decide +kernel
theorem k126_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k126_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k126_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k126_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k126_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s126_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k126_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k126_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k126_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k126_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 126) ((InDA1.TCasaD 6 6 7).getD (126 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k126_6_7_12 k h.1 (by omega)
theorem col126_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 7 v) = true := by decide +kernel
theorem col126 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 126) 126 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col126_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col126_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col126_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s126_3_0
    · exact s126_3_1
    · exact s126_3_2
    · exact s126_3_3
    · exact s126_3_4
    · exact s126_3_5
    · exact s126_3_6
    · exact s126_3_7
  · fin_cases v
    · exact s126_4_0
    · exact s126_4_1
    · exact s126_4_2
    · exact s126_4_3
    · exact s126_4_4
    · exact s126_4_5
    · exact s126_4_6
    · exact s126_4_7
  · fin_cases v
    · exact s126_5_0
    · exact s126_5_1
    · exact s126_5_2
    · exact s126_5_3
    · exact s126_5_4
    · exact s126_5_5
    · exact s126_5_6
    · exact s126_5_7
  · fin_cases v
    · exact s126_6_0
    · exact s126_6_1
    · exact s126_6_2
    · exact s126_6_3
    · exact s126_6_4
    · exact s126_6_5
    · exact s126_6_6
    · exact s126_6_7
  · exact List.all_eq_true.mp col126_7 v (List.mem_finRange v)
theorem col127_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 0 v) = true := by decide +kernel
theorem col127_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 1 v) = true := by decide +kernel
theorem col127_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 2 v) = true := by decide +kernel
theorem s127_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 0 = true := by decide +kernel
theorem s127_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 1 = true := by decide +kernel
theorem s127_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 2 = true := by decide +kernel
theorem k127_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k127_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k127_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s127_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k127_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k127_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k127_3_3_26 k h.1 (by omega)
theorem s127_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 4 = true := by decide +kernel
theorem s127_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 5 = true := by decide +kernel
theorem k127_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k127_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k127_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k127_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k127_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k127_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k127_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k127_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k127_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k127_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k127_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s127_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k127_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k127_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k127_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k127_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k127_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k127_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k127_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k127_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k127_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k127_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k127_3_6_130 k h.1 (by omega)
theorem s127_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 3 7 = true := by decide +kernel
theorem s127_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 0 = true := by decide +kernel
theorem s127_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 1 = true := by decide +kernel
theorem s127_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 2 = true := by decide +kernel
theorem s127_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 3 = true := by decide +kernel
theorem s127_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 4 = true := by decide +kernel
theorem s127_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 5 = true := by decide +kernel
theorem k127_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k127_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k127_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k127_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k127_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k127_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k127_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s127_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k127_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k127_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k127_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k127_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k127_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k127_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k127_4_6_126 k h.1 (by omega)
theorem s127_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 4 7 = true := by decide +kernel
theorem s127_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 0 = true := by decide +kernel
theorem s127_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 1 = true := by decide +kernel
theorem s127_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 2 = true := by decide +kernel
theorem s127_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 3 = true := by decide +kernel
theorem s127_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 4 = true := by decide +kernel
theorem s127_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 5 = true := by decide +kernel
theorem k127_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k127_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k127_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k127_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k127_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k127_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k127_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s127_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k127_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k127_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k127_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k127_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k127_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k127_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 127) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (127 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k127_5_6_126 k h.1 (by omega)
theorem s127_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 5 7 = true := by decide +kernel
theorem s127_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 0 = true := by decide +kernel
theorem s127_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 1 = true := by decide +kernel
theorem s127_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 2 = true := by decide +kernel
theorem s127_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 3 = true := by decide +kernel
theorem s127_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 4 = true := by decide +kernel
theorem s127_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 5 = true := by decide +kernel
theorem s127_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 6 = true := by decide +kernel
theorem k127_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k127_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k127_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k127_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k127_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s127_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k127_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k127_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k127_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k127_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 127) ((InDA1.TCasaD 6 6 7).getD (127 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k127_6_7_12 k h.1 (by omega)
theorem col127_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 7 v) = true := by decide +kernel
theorem col127 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 127) 127 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col127_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col127_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col127_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s127_3_0
    · exact s127_3_1
    · exact s127_3_2
    · exact s127_3_3
    · exact s127_3_4
    · exact s127_3_5
    · exact s127_3_6
    · exact s127_3_7
  · fin_cases v
    · exact s127_4_0
    · exact s127_4_1
    · exact s127_4_2
    · exact s127_4_3
    · exact s127_4_4
    · exact s127_4_5
    · exact s127_4_6
    · exact s127_4_7
  · fin_cases v
    · exact s127_5_0
    · exact s127_5_1
    · exact s127_5_2
    · exact s127_5_3
    · exact s127_5_4
    · exact s127_5_5
    · exact s127_5_6
    · exact s127_5_7
  · fin_cases v
    · exact s127_6_0
    · exact s127_6_1
    · exact s127_6_2
    · exact s127_6_3
    · exact s127_6_4
    · exact s127_6_5
    · exact s127_6_6
    · exact s127_6_7
  · exact List.all_eq_true.mp col127_7 v (List.mem_finRange v)
theorem col128_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 0 v) = true := by decide +kernel
theorem col128_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 1 v) = true := by decide +kernel
theorem col128_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 2 v) = true := by decide +kernel
theorem s128_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 0 = true := by decide +kernel
theorem s128_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 1 = true := by decide +kernel
theorem s128_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 2 = true := by decide +kernel
theorem k128_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k128_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k128_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s128_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k128_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k128_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k128_3_3_26 k h.1 (by omega)
theorem s128_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 4 = true := by decide +kernel
theorem s128_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 5 = true := by decide +kernel
theorem k128_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k128_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k128_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k128_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k128_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k128_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k128_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k128_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k128_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k128_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k128_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s128_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k128_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k128_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k128_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k128_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k128_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k128_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k128_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k128_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k128_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k128_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k128_3_6_130 k h.1 (by omega)
theorem s128_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 3 7 = true := by decide +kernel
theorem s128_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 0 = true := by decide +kernel
theorem s128_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 1 = true := by decide +kernel
theorem s128_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 2 = true := by decide +kernel
theorem s128_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 3 = true := by decide +kernel
theorem s128_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 4 = true := by decide +kernel
theorem s128_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 5 = true := by decide +kernel
theorem k128_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k128_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k128_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k128_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k128_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k128_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k128_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s128_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k128_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k128_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k128_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k128_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k128_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k128_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k128_4_6_126 k h.1 (by omega)
theorem s128_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 4 7 = true := by decide +kernel
theorem s128_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 0 = true := by decide +kernel
theorem s128_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 1 = true := by decide +kernel
theorem s128_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 2 = true := by decide +kernel
theorem s128_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 3 = true := by decide +kernel
theorem s128_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 4 = true := by decide +kernel
theorem s128_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 5 = true := by decide +kernel
theorem k128_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k128_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k128_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k128_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k128_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k128_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k128_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s128_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k128_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k128_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k128_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k128_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k128_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k128_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 128) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (128 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k128_5_6_126 k h.1 (by omega)
theorem s128_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 5 7 = true := by decide +kernel
theorem s128_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 0 = true := by decide +kernel
theorem s128_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 1 = true := by decide +kernel
theorem s128_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 2 = true := by decide +kernel
theorem s128_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 3 = true := by decide +kernel
theorem s128_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 4 = true := by decide +kernel
theorem s128_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 5 = true := by decide +kernel
theorem s128_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 6 = true := by decide +kernel
theorem k128_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k128_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k128_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k128_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k128_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s128_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k128_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k128_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k128_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k128_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 128) ((InDA1.TCasaD 6 6 7).getD (128 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k128_6_7_12 k h.1 (by omega)
theorem col128_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 7 v) = true := by decide +kernel
theorem col128 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 128) 128 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col128_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col128_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col128_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s128_3_0
    · exact s128_3_1
    · exact s128_3_2
    · exact s128_3_3
    · exact s128_3_4
    · exact s128_3_5
    · exact s128_3_6
    · exact s128_3_7
  · fin_cases v
    · exact s128_4_0
    · exact s128_4_1
    · exact s128_4_2
    · exact s128_4_3
    · exact s128_4_4
    · exact s128_4_5
    · exact s128_4_6
    · exact s128_4_7
  · fin_cases v
    · exact s128_5_0
    · exact s128_5_1
    · exact s128_5_2
    · exact s128_5_3
    · exact s128_5_4
    · exact s128_5_5
    · exact s128_5_6
    · exact s128_5_7
  · fin_cases v
    · exact s128_6_0
    · exact s128_6_1
    · exact s128_6_2
    · exact s128_6_3
    · exact s128_6_4
    · exact s128_6_5
    · exact s128_6_6
    · exact s128_6_7
  · exact List.all_eq_true.mp col128_7 v (List.mem_finRange v)
theorem col129_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 0 v) = true := by decide +kernel
theorem col129_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 1 v) = true := by decide +kernel
theorem col129_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 2 v) = true := by decide +kernel
theorem s129_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 0 = true := by decide +kernel
theorem s129_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 1 = true := by decide +kernel
theorem s129_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 2 = true := by decide +kernel
theorem k129_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k129_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k129_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s129_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k129_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k129_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k129_3_3_26 k h.1 (by omega)
theorem s129_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 4 = true := by decide +kernel
theorem s129_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 5 = true := by decide +kernel
theorem k129_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k129_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k129_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k129_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k129_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k129_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k129_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k129_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k129_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k129_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k129_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s129_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k129_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k129_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k129_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k129_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k129_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k129_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k129_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k129_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k129_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k129_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k129_3_6_130 k h.1 (by omega)
theorem s129_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 3 7 = true := by decide +kernel
theorem s129_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 0 = true := by decide +kernel
theorem s129_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 1 = true := by decide +kernel
theorem s129_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 2 = true := by decide +kernel
theorem s129_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 3 = true := by decide +kernel
theorem s129_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 4 = true := by decide +kernel
theorem s129_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 5 = true := by decide +kernel
theorem k129_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k129_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k129_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k129_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k129_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k129_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k129_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s129_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k129_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k129_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k129_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k129_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k129_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k129_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k129_4_6_126 k h.1 (by omega)
theorem s129_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 4 7 = true := by decide +kernel
theorem s129_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 0 = true := by decide +kernel
theorem s129_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 1 = true := by decide +kernel
theorem s129_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 2 = true := by decide +kernel
theorem s129_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 3 = true := by decide +kernel
theorem s129_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 4 = true := by decide +kernel
theorem s129_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 5 = true := by decide +kernel
theorem k129_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k129_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k129_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k129_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k129_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k129_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k129_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s129_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k129_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k129_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k129_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k129_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k129_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k129_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 129) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (129 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k129_5_6_126 k h.1 (by omega)
theorem s129_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 5 7 = true := by decide +kernel
theorem s129_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 0 = true := by decide +kernel
theorem s129_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 1 = true := by decide +kernel
theorem s129_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 2 = true := by decide +kernel
theorem s129_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 3 = true := by decide +kernel
theorem s129_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 4 = true := by decide +kernel
theorem s129_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 5 = true := by decide +kernel
theorem s129_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 6 = true := by decide +kernel
theorem k129_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k129_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k129_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k129_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k129_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s129_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k129_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k129_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k129_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k129_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 129) ((InDA1.TCasaD 6 6 7).getD (129 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k129_6_7_12 k h.1 (by omega)
theorem col129_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 7 v) = true := by decide +kernel
theorem col129 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 129) 129 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col129_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col129_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col129_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s129_3_0
    · exact s129_3_1
    · exact s129_3_2
    · exact s129_3_3
    · exact s129_3_4
    · exact s129_3_5
    · exact s129_3_6
    · exact s129_3_7
  · fin_cases v
    · exact s129_4_0
    · exact s129_4_1
    · exact s129_4_2
    · exact s129_4_3
    · exact s129_4_4
    · exact s129_4_5
    · exact s129_4_6
    · exact s129_4_7
  · fin_cases v
    · exact s129_5_0
    · exact s129_5_1
    · exact s129_5_2
    · exact s129_5_3
    · exact s129_5_4
    · exact s129_5_5
    · exact s129_5_6
    · exact s129_5_7
  · fin_cases v
    · exact s129_6_0
    · exact s129_6_1
    · exact s129_6_2
    · exact s129_6_3
    · exact s129_6_4
    · exact s129_6_5
    · exact s129_6_6
    · exact s129_6_7
  · exact List.all_eq_true.mp col129_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
