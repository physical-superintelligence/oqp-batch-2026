module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [120, 125). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col120_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 0 v) = true := by decide +kernel
theorem col120_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 1 v) = true := by decide +kernel
theorem col120_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 2 v) = true := by decide +kernel
theorem s120_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 0 = true := by decide +kernel
theorem s120_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 1 = true := by decide +kernel
theorem s120_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 2 = true := by decide +kernel
theorem k120_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k120_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k120_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s120_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k120_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k120_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k120_3_3_26 k h.1 (by omega)
theorem s120_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 4 = true := by decide +kernel
theorem s120_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 5 = true := by decide +kernel
theorem k120_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k120_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k120_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k120_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k120_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k120_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k120_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k120_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k120_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k120_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k120_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s120_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k120_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k120_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k120_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k120_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k120_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k120_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k120_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k120_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k120_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k120_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k120_3_6_130 k h.1 (by omega)
theorem s120_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 3 7 = true := by decide +kernel
theorem s120_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 0 = true := by decide +kernel
theorem s120_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 1 = true := by decide +kernel
theorem s120_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 2 = true := by decide +kernel
theorem s120_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 3 = true := by decide +kernel
theorem s120_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 4 = true := by decide +kernel
theorem s120_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 5 = true := by decide +kernel
theorem k120_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k120_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k120_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k120_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k120_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k120_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k120_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s120_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k120_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k120_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k120_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k120_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k120_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k120_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k120_4_6_126 k h.1 (by omega)
theorem s120_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 4 7 = true := by decide +kernel
theorem s120_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 0 = true := by decide +kernel
theorem s120_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 1 = true := by decide +kernel
theorem s120_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 2 = true := by decide +kernel
theorem s120_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 3 = true := by decide +kernel
theorem s120_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 4 = true := by decide +kernel
theorem s120_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 5 = true := by decide +kernel
theorem k120_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k120_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k120_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k120_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k120_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k120_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k120_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s120_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k120_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k120_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k120_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k120_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k120_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k120_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 120) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (120 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k120_5_6_126 k h.1 (by omega)
theorem s120_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 5 7 = true := by decide +kernel
theorem s120_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 0 = true := by decide +kernel
theorem s120_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 1 = true := by decide +kernel
theorem s120_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 2 = true := by decide +kernel
theorem s120_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 3 = true := by decide +kernel
theorem s120_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 4 = true := by decide +kernel
theorem s120_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 5 = true := by decide +kernel
theorem s120_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 6 = true := by decide +kernel
theorem k120_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k120_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k120_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k120_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k120_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s120_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k120_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k120_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k120_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k120_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 120) ((InDA1.TCasaD 6 6 7).getD (120 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k120_6_7_12 k h.1 (by omega)
theorem col120_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 7 v) = true := by decide +kernel
theorem col120 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 120) 120 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col120_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col120_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col120_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s120_3_0
    · exact s120_3_1
    · exact s120_3_2
    · exact s120_3_3
    · exact s120_3_4
    · exact s120_3_5
    · exact s120_3_6
    · exact s120_3_7
  · fin_cases v
    · exact s120_4_0
    · exact s120_4_1
    · exact s120_4_2
    · exact s120_4_3
    · exact s120_4_4
    · exact s120_4_5
    · exact s120_4_6
    · exact s120_4_7
  · fin_cases v
    · exact s120_5_0
    · exact s120_5_1
    · exact s120_5_2
    · exact s120_5_3
    · exact s120_5_4
    · exact s120_5_5
    · exact s120_5_6
    · exact s120_5_7
  · fin_cases v
    · exact s120_6_0
    · exact s120_6_1
    · exact s120_6_2
    · exact s120_6_3
    · exact s120_6_4
    · exact s120_6_5
    · exact s120_6_6
    · exact s120_6_7
  · exact List.all_eq_true.mp col120_7 v (List.mem_finRange v)
theorem col121_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 0 v) = true := by decide +kernel
theorem col121_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 1 v) = true := by decide +kernel
theorem col121_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 2 v) = true := by decide +kernel
theorem s121_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 0 = true := by decide +kernel
theorem s121_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 1 = true := by decide +kernel
theorem s121_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 2 = true := by decide +kernel
theorem k121_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k121_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k121_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s121_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k121_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k121_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k121_3_3_26 k h.1 (by omega)
theorem s121_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 4 = true := by decide +kernel
theorem s121_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 5 = true := by decide +kernel
theorem k121_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k121_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k121_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k121_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k121_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k121_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k121_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k121_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k121_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k121_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k121_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s121_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k121_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k121_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k121_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k121_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k121_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k121_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k121_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k121_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k121_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k121_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k121_3_6_130 k h.1 (by omega)
theorem s121_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 3 7 = true := by decide +kernel
theorem s121_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 0 = true := by decide +kernel
theorem s121_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 1 = true := by decide +kernel
theorem s121_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 2 = true := by decide +kernel
theorem s121_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 3 = true := by decide +kernel
theorem s121_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 4 = true := by decide +kernel
theorem s121_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 5 = true := by decide +kernel
theorem k121_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k121_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k121_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k121_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k121_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k121_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k121_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s121_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k121_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k121_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k121_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k121_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k121_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k121_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k121_4_6_126 k h.1 (by omega)
theorem s121_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 4 7 = true := by decide +kernel
theorem s121_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 0 = true := by decide +kernel
theorem s121_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 1 = true := by decide +kernel
theorem s121_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 2 = true := by decide +kernel
theorem s121_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 3 = true := by decide +kernel
theorem s121_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 4 = true := by decide +kernel
theorem s121_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 5 = true := by decide +kernel
theorem k121_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k121_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k121_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k121_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k121_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k121_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k121_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s121_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k121_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k121_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k121_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k121_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k121_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k121_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 121) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (121 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k121_5_6_126 k h.1 (by omega)
theorem s121_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 5 7 = true := by decide +kernel
theorem s121_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 0 = true := by decide +kernel
theorem s121_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 1 = true := by decide +kernel
theorem s121_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 2 = true := by decide +kernel
theorem s121_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 3 = true := by decide +kernel
theorem s121_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 4 = true := by decide +kernel
theorem s121_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 5 = true := by decide +kernel
theorem s121_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 6 = true := by decide +kernel
theorem k121_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k121_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k121_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k121_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k121_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s121_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k121_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k121_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k121_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k121_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 121) ((InDA1.TCasaD 6 6 7).getD (121 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k121_6_7_12 k h.1 (by omega)
theorem col121_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 7 v) = true := by decide +kernel
theorem col121 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 121) 121 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col121_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col121_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col121_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s121_3_0
    · exact s121_3_1
    · exact s121_3_2
    · exact s121_3_3
    · exact s121_3_4
    · exact s121_3_5
    · exact s121_3_6
    · exact s121_3_7
  · fin_cases v
    · exact s121_4_0
    · exact s121_4_1
    · exact s121_4_2
    · exact s121_4_3
    · exact s121_4_4
    · exact s121_4_5
    · exact s121_4_6
    · exact s121_4_7
  · fin_cases v
    · exact s121_5_0
    · exact s121_5_1
    · exact s121_5_2
    · exact s121_5_3
    · exact s121_5_4
    · exact s121_5_5
    · exact s121_5_6
    · exact s121_5_7
  · fin_cases v
    · exact s121_6_0
    · exact s121_6_1
    · exact s121_6_2
    · exact s121_6_3
    · exact s121_6_4
    · exact s121_6_5
    · exact s121_6_6
    · exact s121_6_7
  · exact List.all_eq_true.mp col121_7 v (List.mem_finRange v)
theorem col122_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 0 v) = true := by decide +kernel
theorem col122_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 1 v) = true := by decide +kernel
theorem col122_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 2 v) = true := by decide +kernel
theorem s122_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 0 = true := by decide +kernel
theorem s122_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 1 = true := by decide +kernel
theorem s122_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 2 = true := by decide +kernel
theorem k122_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k122_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k122_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s122_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k122_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k122_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k122_3_3_26 k h.1 (by omega)
theorem s122_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 4 = true := by decide +kernel
theorem s122_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 5 = true := by decide +kernel
theorem k122_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k122_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k122_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k122_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k122_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k122_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k122_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k122_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k122_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k122_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k122_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s122_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k122_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k122_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k122_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k122_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k122_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k122_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k122_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k122_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k122_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k122_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k122_3_6_130 k h.1 (by omega)
theorem s122_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 3 7 = true := by decide +kernel
theorem s122_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 0 = true := by decide +kernel
theorem s122_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 1 = true := by decide +kernel
theorem s122_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 2 = true := by decide +kernel
theorem s122_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 3 = true := by decide +kernel
theorem s122_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 4 = true := by decide +kernel
theorem s122_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 5 = true := by decide +kernel
theorem k122_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k122_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k122_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k122_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k122_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k122_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k122_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s122_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k122_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k122_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k122_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k122_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k122_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k122_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k122_4_6_126 k h.1 (by omega)
theorem s122_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 4 7 = true := by decide +kernel
theorem s122_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 0 = true := by decide +kernel
theorem s122_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 1 = true := by decide +kernel
theorem s122_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 2 = true := by decide +kernel
theorem s122_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 3 = true := by decide +kernel
theorem s122_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 4 = true := by decide +kernel
theorem s122_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 5 = true := by decide +kernel
theorem k122_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k122_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k122_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k122_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k122_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k122_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k122_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s122_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k122_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k122_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k122_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k122_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k122_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k122_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 122) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (122 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k122_5_6_126 k h.1 (by omega)
theorem s122_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 5 7 = true := by decide +kernel
theorem s122_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 0 = true := by decide +kernel
theorem s122_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 1 = true := by decide +kernel
theorem s122_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 2 = true := by decide +kernel
theorem s122_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 3 = true := by decide +kernel
theorem s122_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 4 = true := by decide +kernel
theorem s122_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 5 = true := by decide +kernel
theorem s122_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 6 = true := by decide +kernel
theorem k122_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k122_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k122_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k122_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k122_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s122_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k122_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k122_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k122_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k122_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 122) ((InDA1.TCasaD 6 6 7).getD (122 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k122_6_7_12 k h.1 (by omega)
theorem col122_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 7 v) = true := by decide +kernel
theorem col122 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 122) 122 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col122_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col122_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col122_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s122_3_0
    · exact s122_3_1
    · exact s122_3_2
    · exact s122_3_3
    · exact s122_3_4
    · exact s122_3_5
    · exact s122_3_6
    · exact s122_3_7
  · fin_cases v
    · exact s122_4_0
    · exact s122_4_1
    · exact s122_4_2
    · exact s122_4_3
    · exact s122_4_4
    · exact s122_4_5
    · exact s122_4_6
    · exact s122_4_7
  · fin_cases v
    · exact s122_5_0
    · exact s122_5_1
    · exact s122_5_2
    · exact s122_5_3
    · exact s122_5_4
    · exact s122_5_5
    · exact s122_5_6
    · exact s122_5_7
  · fin_cases v
    · exact s122_6_0
    · exact s122_6_1
    · exact s122_6_2
    · exact s122_6_3
    · exact s122_6_4
    · exact s122_6_5
    · exact s122_6_6
    · exact s122_6_7
  · exact List.all_eq_true.mp col122_7 v (List.mem_finRange v)
theorem col123_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 0 v) = true := by decide +kernel
theorem col123_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 1 v) = true := by decide +kernel
theorem col123_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 2 v) = true := by decide +kernel
theorem s123_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 0 = true := by decide +kernel
theorem s123_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 1 = true := by decide +kernel
theorem s123_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 2 = true := by decide +kernel
theorem k123_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k123_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k123_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s123_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k123_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k123_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k123_3_3_26 k h.1 (by omega)
theorem s123_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 4 = true := by decide +kernel
theorem s123_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 5 = true := by decide +kernel
theorem k123_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k123_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k123_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k123_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k123_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k123_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k123_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k123_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k123_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k123_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k123_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s123_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k123_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k123_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k123_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k123_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k123_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k123_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k123_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k123_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k123_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k123_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k123_3_6_130 k h.1 (by omega)
theorem s123_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 3 7 = true := by decide +kernel
theorem s123_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 0 = true := by decide +kernel
theorem s123_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 1 = true := by decide +kernel
theorem s123_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 2 = true := by decide +kernel
theorem s123_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 3 = true := by decide +kernel
theorem s123_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 4 = true := by decide +kernel
theorem s123_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 5 = true := by decide +kernel
theorem k123_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k123_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k123_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k123_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k123_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k123_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k123_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s123_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k123_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k123_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k123_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k123_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k123_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k123_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k123_4_6_126 k h.1 (by omega)
theorem s123_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 4 7 = true := by decide +kernel
theorem s123_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 0 = true := by decide +kernel
theorem s123_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 1 = true := by decide +kernel
theorem s123_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 2 = true := by decide +kernel
theorem s123_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 3 = true := by decide +kernel
theorem s123_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 4 = true := by decide +kernel
theorem s123_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 5 = true := by decide +kernel
theorem k123_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k123_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k123_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k123_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k123_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k123_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k123_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s123_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k123_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k123_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k123_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k123_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k123_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k123_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 123) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (123 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k123_5_6_126 k h.1 (by omega)
theorem s123_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 5 7 = true := by decide +kernel
theorem s123_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 0 = true := by decide +kernel
theorem s123_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 1 = true := by decide +kernel
theorem s123_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 2 = true := by decide +kernel
theorem s123_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 3 = true := by decide +kernel
theorem s123_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 4 = true := by decide +kernel
theorem s123_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 5 = true := by decide +kernel
theorem s123_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 6 = true := by decide +kernel
theorem k123_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k123_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k123_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k123_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k123_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s123_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k123_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k123_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k123_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k123_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 123) ((InDA1.TCasaD 6 6 7).getD (123 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k123_6_7_12 k h.1 (by omega)
theorem col123_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 7 v) = true := by decide +kernel
theorem col123 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 123) 123 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col123_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col123_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col123_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s123_3_0
    · exact s123_3_1
    · exact s123_3_2
    · exact s123_3_3
    · exact s123_3_4
    · exact s123_3_5
    · exact s123_3_6
    · exact s123_3_7
  · fin_cases v
    · exact s123_4_0
    · exact s123_4_1
    · exact s123_4_2
    · exact s123_4_3
    · exact s123_4_4
    · exact s123_4_5
    · exact s123_4_6
    · exact s123_4_7
  · fin_cases v
    · exact s123_5_0
    · exact s123_5_1
    · exact s123_5_2
    · exact s123_5_3
    · exact s123_5_4
    · exact s123_5_5
    · exact s123_5_6
    · exact s123_5_7
  · fin_cases v
    · exact s123_6_0
    · exact s123_6_1
    · exact s123_6_2
    · exact s123_6_3
    · exact s123_6_4
    · exact s123_6_5
    · exact s123_6_6
    · exact s123_6_7
  · exact List.all_eq_true.mp col123_7 v (List.mem_finRange v)
theorem col124_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 0 v) = true := by decide +kernel
theorem col124_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 1 v) = true := by decide +kernel
theorem col124_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 2 v) = true := by decide +kernel
theorem s124_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 0 = true := by decide +kernel
theorem s124_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 1 = true := by decide +kernel
theorem s124_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 2 = true := by decide +kernel
theorem k124_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k124_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k124_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s124_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k124_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k124_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k124_3_3_26 k h.1 (by omega)
theorem s124_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 4 = true := by decide +kernel
theorem s124_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 5 = true := by decide +kernel
theorem k124_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k124_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k124_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k124_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k124_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k124_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k124_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k124_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k124_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k124_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k124_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s124_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k124_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k124_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k124_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k124_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k124_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k124_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k124_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k124_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k124_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k124_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k124_3_6_130 k h.1 (by omega)
theorem s124_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 3 7 = true := by decide +kernel
theorem s124_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 0 = true := by decide +kernel
theorem s124_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 1 = true := by decide +kernel
theorem s124_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 2 = true := by decide +kernel
theorem s124_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 3 = true := by decide +kernel
theorem s124_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 4 = true := by decide +kernel
theorem s124_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 5 = true := by decide +kernel
theorem k124_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k124_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k124_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k124_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k124_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k124_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k124_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s124_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k124_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k124_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k124_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k124_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k124_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k124_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k124_4_6_126 k h.1 (by omega)
theorem s124_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 4 7 = true := by decide +kernel
theorem s124_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 0 = true := by decide +kernel
theorem s124_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 1 = true := by decide +kernel
theorem s124_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 2 = true := by decide +kernel
theorem s124_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 3 = true := by decide +kernel
theorem s124_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 4 = true := by decide +kernel
theorem s124_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 5 = true := by decide +kernel
theorem k124_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k124_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k124_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k124_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k124_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k124_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k124_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s124_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k124_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k124_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k124_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k124_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k124_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k124_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 124) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (124 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k124_5_6_126 k h.1 (by omega)
theorem s124_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 5 7 = true := by decide +kernel
theorem s124_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 0 = true := by decide +kernel
theorem s124_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 1 = true := by decide +kernel
theorem s124_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 2 = true := by decide +kernel
theorem s124_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 3 = true := by decide +kernel
theorem s124_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 4 = true := by decide +kernel
theorem s124_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 5 = true := by decide +kernel
theorem s124_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 6 = true := by decide +kernel
theorem k124_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k124_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k124_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k124_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k124_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s124_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k124_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k124_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k124_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k124_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 124) ((InDA1.TCasaD 6 6 7).getD (124 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k124_6_7_12 k h.1 (by omega)
theorem col124_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 7 v) = true := by decide +kernel
theorem col124 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 124) 124 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col124_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col124_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col124_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s124_3_0
    · exact s124_3_1
    · exact s124_3_2
    · exact s124_3_3
    · exact s124_3_4
    · exact s124_3_5
    · exact s124_3_6
    · exact s124_3_7
  · fin_cases v
    · exact s124_4_0
    · exact s124_4_1
    · exact s124_4_2
    · exact s124_4_3
    · exact s124_4_4
    · exact s124_4_5
    · exact s124_4_6
    · exact s124_4_7
  · fin_cases v
    · exact s124_5_0
    · exact s124_5_1
    · exact s124_5_2
    · exact s124_5_3
    · exact s124_5_4
    · exact s124_5_5
    · exact s124_5_6
    · exact s124_5_7
  · fin_cases v
    · exact s124_6_0
    · exact s124_6_1
    · exact s124_6_2
    · exact s124_6_3
    · exact s124_6_4
    · exact s124_6_5
    · exact s124_6_6
    · exact s124_6_7
  · exact List.all_eq_true.mp col124_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
