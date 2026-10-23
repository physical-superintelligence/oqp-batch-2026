module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [210, 215). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col210_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 0 v) = true := by decide +kernel
theorem col210_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 1 v) = true := by decide +kernel
theorem col210_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 2 v) = true := by decide +kernel
theorem s210_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 0 = true := by decide +kernel
theorem s210_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 1 = true := by decide +kernel
theorem s210_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 2 = true := by decide +kernel
theorem k210_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k210_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k210_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s210_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k210_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k210_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k210_3_3_26 k h.1 (by omega)
theorem s210_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 4 = true := by decide +kernel
theorem s210_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 5 = true := by decide +kernel
theorem k210_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k210_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k210_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k210_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k210_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k210_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k210_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k210_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k210_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k210_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k210_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s210_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k210_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k210_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k210_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k210_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k210_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k210_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k210_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k210_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k210_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k210_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k210_3_6_130 k h.1 (by omega)
theorem s210_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 3 7 = true := by decide +kernel
theorem s210_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 0 = true := by decide +kernel
theorem s210_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 1 = true := by decide +kernel
theorem s210_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 2 = true := by decide +kernel
theorem s210_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 3 = true := by decide +kernel
theorem s210_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 4 = true := by decide +kernel
theorem s210_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 5 = true := by decide +kernel
theorem k210_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k210_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k210_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k210_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k210_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k210_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k210_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s210_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k210_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k210_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k210_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k210_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k210_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k210_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k210_4_6_126 k h.1 (by omega)
theorem s210_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 4 7 = true := by decide +kernel
theorem s210_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 0 = true := by decide +kernel
theorem s210_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 1 = true := by decide +kernel
theorem s210_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 2 = true := by decide +kernel
theorem s210_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 3 = true := by decide +kernel
theorem s210_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 4 = true := by decide +kernel
theorem s210_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 5 = true := by decide +kernel
theorem k210_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k210_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k210_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k210_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k210_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k210_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k210_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s210_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k210_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k210_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k210_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k210_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k210_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k210_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 210) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (210 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k210_5_6_126 k h.1 (by omega)
theorem s210_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 5 7 = true := by decide +kernel
theorem s210_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 0 = true := by decide +kernel
theorem s210_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 1 = true := by decide +kernel
theorem s210_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 2 = true := by decide +kernel
theorem s210_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 3 = true := by decide +kernel
theorem s210_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 4 = true := by decide +kernel
theorem s210_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 5 = true := by decide +kernel
theorem s210_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 6 = true := by decide +kernel
theorem k210_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k210_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k210_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k210_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k210_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s210_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k210_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k210_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k210_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k210_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 210) ((InDA1.TCasaD 6 6 7).getD (210 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k210_6_7_12 k h.1 (by omega)
theorem col210_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 7 v) = true := by decide +kernel
theorem col210 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 210) 210 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col210_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col210_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col210_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s210_3_0
    · exact s210_3_1
    · exact s210_3_2
    · exact s210_3_3
    · exact s210_3_4
    · exact s210_3_5
    · exact s210_3_6
    · exact s210_3_7
  · fin_cases v
    · exact s210_4_0
    · exact s210_4_1
    · exact s210_4_2
    · exact s210_4_3
    · exact s210_4_4
    · exact s210_4_5
    · exact s210_4_6
    · exact s210_4_7
  · fin_cases v
    · exact s210_5_0
    · exact s210_5_1
    · exact s210_5_2
    · exact s210_5_3
    · exact s210_5_4
    · exact s210_5_5
    · exact s210_5_6
    · exact s210_5_7
  · fin_cases v
    · exact s210_6_0
    · exact s210_6_1
    · exact s210_6_2
    · exact s210_6_3
    · exact s210_6_4
    · exact s210_6_5
    · exact s210_6_6
    · exact s210_6_7
  · exact List.all_eq_true.mp col210_7 v (List.mem_finRange v)
theorem col211_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 0 v) = true := by decide +kernel
theorem col211_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 1 v) = true := by decide +kernel
theorem col211_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 2 v) = true := by decide +kernel
theorem s211_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 0 = true := by decide +kernel
theorem s211_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 1 = true := by decide +kernel
theorem s211_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 2 = true := by decide +kernel
theorem k211_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k211_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k211_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s211_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k211_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k211_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k211_3_3_26 k h.1 (by omega)
theorem s211_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 4 = true := by decide +kernel
theorem s211_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 5 = true := by decide +kernel
theorem k211_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k211_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k211_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k211_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k211_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k211_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k211_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k211_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k211_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k211_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k211_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s211_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k211_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k211_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k211_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k211_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k211_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k211_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k211_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k211_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k211_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k211_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k211_3_6_130 k h.1 (by omega)
theorem s211_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 3 7 = true := by decide +kernel
theorem s211_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 0 = true := by decide +kernel
theorem s211_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 1 = true := by decide +kernel
theorem s211_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 2 = true := by decide +kernel
theorem s211_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 3 = true := by decide +kernel
theorem s211_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 4 = true := by decide +kernel
theorem s211_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 5 = true := by decide +kernel
theorem k211_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k211_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k211_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k211_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k211_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k211_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k211_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s211_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k211_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k211_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k211_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k211_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k211_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k211_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k211_4_6_126 k h.1 (by omega)
theorem s211_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 4 7 = true := by decide +kernel
theorem s211_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 0 = true := by decide +kernel
theorem s211_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 1 = true := by decide +kernel
theorem s211_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 2 = true := by decide +kernel
theorem s211_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 3 = true := by decide +kernel
theorem s211_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 4 = true := by decide +kernel
theorem s211_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 5 = true := by decide +kernel
theorem k211_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k211_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k211_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k211_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k211_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k211_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k211_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s211_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k211_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k211_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k211_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k211_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k211_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k211_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 211) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (211 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k211_5_6_126 k h.1 (by omega)
theorem s211_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 5 7 = true := by decide +kernel
theorem s211_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 0 = true := by decide +kernel
theorem s211_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 1 = true := by decide +kernel
theorem s211_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 2 = true := by decide +kernel
theorem s211_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 3 = true := by decide +kernel
theorem s211_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 4 = true := by decide +kernel
theorem s211_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 5 = true := by decide +kernel
theorem s211_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 6 = true := by decide +kernel
theorem k211_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k211_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k211_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k211_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k211_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s211_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k211_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k211_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k211_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k211_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 211) ((InDA1.TCasaD 6 6 7).getD (211 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k211_6_7_12 k h.1 (by omega)
theorem col211_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 7 v) = true := by decide +kernel
theorem col211 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 211) 211 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col211_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col211_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col211_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s211_3_0
    · exact s211_3_1
    · exact s211_3_2
    · exact s211_3_3
    · exact s211_3_4
    · exact s211_3_5
    · exact s211_3_6
    · exact s211_3_7
  · fin_cases v
    · exact s211_4_0
    · exact s211_4_1
    · exact s211_4_2
    · exact s211_4_3
    · exact s211_4_4
    · exact s211_4_5
    · exact s211_4_6
    · exact s211_4_7
  · fin_cases v
    · exact s211_5_0
    · exact s211_5_1
    · exact s211_5_2
    · exact s211_5_3
    · exact s211_5_4
    · exact s211_5_5
    · exact s211_5_6
    · exact s211_5_7
  · fin_cases v
    · exact s211_6_0
    · exact s211_6_1
    · exact s211_6_2
    · exact s211_6_3
    · exact s211_6_4
    · exact s211_6_5
    · exact s211_6_6
    · exact s211_6_7
  · exact List.all_eq_true.mp col211_7 v (List.mem_finRange v)
theorem col212_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 0 v) = true := by decide +kernel
theorem col212_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 1 v) = true := by decide +kernel
theorem col212_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 2 v) = true := by decide +kernel
theorem s212_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 0 = true := by decide +kernel
theorem s212_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 1 = true := by decide +kernel
theorem s212_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 2 = true := by decide +kernel
theorem k212_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k212_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k212_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s212_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k212_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k212_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k212_3_3_26 k h.1 (by omega)
theorem s212_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 4 = true := by decide +kernel
theorem s212_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 5 = true := by decide +kernel
theorem k212_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k212_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k212_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k212_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k212_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k212_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k212_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k212_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k212_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k212_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k212_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s212_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k212_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k212_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k212_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k212_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k212_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k212_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k212_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k212_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k212_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k212_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k212_3_6_130 k h.1 (by omega)
theorem s212_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 3 7 = true := by decide +kernel
theorem s212_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 0 = true := by decide +kernel
theorem s212_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 1 = true := by decide +kernel
theorem s212_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 2 = true := by decide +kernel
theorem s212_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 3 = true := by decide +kernel
theorem s212_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 4 = true := by decide +kernel
theorem s212_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 5 = true := by decide +kernel
theorem k212_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k212_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k212_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k212_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k212_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k212_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k212_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s212_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k212_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k212_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k212_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k212_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k212_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k212_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k212_4_6_126 k h.1 (by omega)
theorem s212_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 4 7 = true := by decide +kernel
theorem s212_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 0 = true := by decide +kernel
theorem s212_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 1 = true := by decide +kernel
theorem s212_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 2 = true := by decide +kernel
theorem s212_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 3 = true := by decide +kernel
theorem s212_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 4 = true := by decide +kernel
theorem s212_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 5 = true := by decide +kernel
theorem k212_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k212_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k212_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k212_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k212_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k212_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k212_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s212_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k212_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k212_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k212_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k212_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k212_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k212_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 212) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (212 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k212_5_6_126 k h.1 (by omega)
theorem s212_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 5 7 = true := by decide +kernel
theorem s212_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 0 = true := by decide +kernel
theorem s212_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 1 = true := by decide +kernel
theorem s212_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 2 = true := by decide +kernel
theorem s212_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 3 = true := by decide +kernel
theorem s212_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 4 = true := by decide +kernel
theorem s212_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 5 = true := by decide +kernel
theorem s212_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 6 = true := by decide +kernel
theorem k212_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k212_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k212_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k212_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k212_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s212_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k212_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k212_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k212_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k212_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 212) ((InDA1.TCasaD 6 6 7).getD (212 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k212_6_7_12 k h.1 (by omega)
theorem col212_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 7 v) = true := by decide +kernel
theorem col212 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 212) 212 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col212_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col212_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col212_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s212_3_0
    · exact s212_3_1
    · exact s212_3_2
    · exact s212_3_3
    · exact s212_3_4
    · exact s212_3_5
    · exact s212_3_6
    · exact s212_3_7
  · fin_cases v
    · exact s212_4_0
    · exact s212_4_1
    · exact s212_4_2
    · exact s212_4_3
    · exact s212_4_4
    · exact s212_4_5
    · exact s212_4_6
    · exact s212_4_7
  · fin_cases v
    · exact s212_5_0
    · exact s212_5_1
    · exact s212_5_2
    · exact s212_5_3
    · exact s212_5_4
    · exact s212_5_5
    · exact s212_5_6
    · exact s212_5_7
  · fin_cases v
    · exact s212_6_0
    · exact s212_6_1
    · exact s212_6_2
    · exact s212_6_3
    · exact s212_6_4
    · exact s212_6_5
    · exact s212_6_6
    · exact s212_6_7
  · exact List.all_eq_true.mp col212_7 v (List.mem_finRange v)
theorem col213_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 0 v) = true := by decide +kernel
theorem col213_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 1 v) = true := by decide +kernel
theorem col213_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 2 v) = true := by decide +kernel
theorem s213_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 0 = true := by decide +kernel
theorem s213_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 1 = true := by decide +kernel
theorem s213_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 2 = true := by decide +kernel
theorem k213_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k213_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k213_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s213_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k213_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k213_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k213_3_3_26 k h.1 (by omega)
theorem s213_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 4 = true := by decide +kernel
theorem s213_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 5 = true := by decide +kernel
theorem k213_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k213_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k213_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k213_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k213_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k213_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k213_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k213_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k213_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k213_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k213_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s213_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k213_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k213_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k213_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k213_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k213_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k213_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k213_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k213_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k213_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k213_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k213_3_6_130 k h.1 (by omega)
theorem s213_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 3 7 = true := by decide +kernel
theorem s213_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 0 = true := by decide +kernel
theorem s213_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 1 = true := by decide +kernel
theorem s213_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 2 = true := by decide +kernel
theorem s213_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 3 = true := by decide +kernel
theorem s213_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 4 = true := by decide +kernel
theorem s213_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 5 = true := by decide +kernel
theorem k213_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k213_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k213_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k213_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k213_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k213_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k213_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s213_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k213_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k213_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k213_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k213_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k213_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k213_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k213_4_6_126 k h.1 (by omega)
theorem s213_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 4 7 = true := by decide +kernel
theorem s213_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 0 = true := by decide +kernel
theorem s213_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 1 = true := by decide +kernel
theorem s213_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 2 = true := by decide +kernel
theorem s213_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 3 = true := by decide +kernel
theorem s213_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 4 = true := by decide +kernel
theorem s213_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 5 = true := by decide +kernel
theorem k213_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k213_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k213_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k213_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k213_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k213_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k213_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s213_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k213_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k213_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k213_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k213_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k213_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k213_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 213) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (213 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k213_5_6_126 k h.1 (by omega)
theorem s213_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 5 7 = true := by decide +kernel
theorem s213_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 0 = true := by decide +kernel
theorem s213_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 1 = true := by decide +kernel
theorem s213_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 2 = true := by decide +kernel
theorem s213_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 3 = true := by decide +kernel
theorem s213_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 4 = true := by decide +kernel
theorem s213_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 5 = true := by decide +kernel
theorem s213_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 6 = true := by decide +kernel
theorem k213_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k213_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k213_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k213_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k213_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s213_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k213_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k213_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k213_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k213_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 213) ((InDA1.TCasaD 6 6 7).getD (213 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k213_6_7_12 k h.1 (by omega)
theorem col213_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 7 v) = true := by decide +kernel
theorem col213 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 213) 213 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col213_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col213_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col213_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s213_3_0
    · exact s213_3_1
    · exact s213_3_2
    · exact s213_3_3
    · exact s213_3_4
    · exact s213_3_5
    · exact s213_3_6
    · exact s213_3_7
  · fin_cases v
    · exact s213_4_0
    · exact s213_4_1
    · exact s213_4_2
    · exact s213_4_3
    · exact s213_4_4
    · exact s213_4_5
    · exact s213_4_6
    · exact s213_4_7
  · fin_cases v
    · exact s213_5_0
    · exact s213_5_1
    · exact s213_5_2
    · exact s213_5_3
    · exact s213_5_4
    · exact s213_5_5
    · exact s213_5_6
    · exact s213_5_7
  · fin_cases v
    · exact s213_6_0
    · exact s213_6_1
    · exact s213_6_2
    · exact s213_6_3
    · exact s213_6_4
    · exact s213_6_5
    · exact s213_6_6
    · exact s213_6_7
  · exact List.all_eq_true.mp col213_7 v (List.mem_finRange v)
theorem col214_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 0 v) = true := by decide +kernel
theorem col214_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 1 v) = true := by decide +kernel
theorem col214_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 2 v) = true := by decide +kernel
theorem s214_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 0 = true := by decide +kernel
theorem s214_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 1 = true := by decide +kernel
theorem s214_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 2 = true := by decide +kernel
theorem k214_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k214_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k214_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s214_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k214_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k214_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k214_3_3_26 k h.1 (by omega)
theorem s214_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 4 = true := by decide +kernel
theorem s214_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 5 = true := by decide +kernel
theorem k214_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k214_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k214_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k214_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k214_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k214_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k214_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k214_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k214_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k214_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k214_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s214_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k214_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k214_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k214_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k214_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k214_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k214_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k214_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k214_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k214_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k214_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k214_3_6_130 k h.1 (by omega)
theorem s214_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 3 7 = true := by decide +kernel
theorem s214_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 0 = true := by decide +kernel
theorem s214_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 1 = true := by decide +kernel
theorem s214_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 2 = true := by decide +kernel
theorem s214_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 3 = true := by decide +kernel
theorem s214_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 4 = true := by decide +kernel
theorem s214_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 5 = true := by decide +kernel
theorem k214_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k214_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k214_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k214_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k214_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k214_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k214_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s214_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k214_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k214_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k214_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k214_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k214_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k214_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k214_4_6_126 k h.1 (by omega)
theorem s214_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 4 7 = true := by decide +kernel
theorem s214_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 0 = true := by decide +kernel
theorem s214_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 1 = true := by decide +kernel
theorem s214_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 2 = true := by decide +kernel
theorem s214_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 3 = true := by decide +kernel
theorem s214_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 4 = true := by decide +kernel
theorem s214_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 5 = true := by decide +kernel
theorem k214_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k214_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k214_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k214_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k214_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k214_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k214_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s214_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k214_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k214_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k214_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k214_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k214_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k214_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 214) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (214 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k214_5_6_126 k h.1 (by omega)
theorem s214_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 5 7 = true := by decide +kernel
theorem s214_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 0 = true := by decide +kernel
theorem s214_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 1 = true := by decide +kernel
theorem s214_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 2 = true := by decide +kernel
theorem s214_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 3 = true := by decide +kernel
theorem s214_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 4 = true := by decide +kernel
theorem s214_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 5 = true := by decide +kernel
theorem s214_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 6 = true := by decide +kernel
theorem k214_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k214_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k214_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k214_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k214_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s214_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k214_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k214_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k214_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k214_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 214) ((InDA1.TCasaD 6 6 7).getD (214 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k214_6_7_12 k h.1 (by omega)
theorem col214_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 7 v) = true := by decide +kernel
theorem col214 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 214) 214 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col214_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col214_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col214_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s214_3_0
    · exact s214_3_1
    · exact s214_3_2
    · exact s214_3_3
    · exact s214_3_4
    · exact s214_3_5
    · exact s214_3_6
    · exact s214_3_7
  · fin_cases v
    · exact s214_4_0
    · exact s214_4_1
    · exact s214_4_2
    · exact s214_4_3
    · exact s214_4_4
    · exact s214_4_5
    · exact s214_4_6
    · exact s214_4_7
  · fin_cases v
    · exact s214_5_0
    · exact s214_5_1
    · exact s214_5_2
    · exact s214_5_3
    · exact s214_5_4
    · exact s214_5_5
    · exact s214_5_6
    · exact s214_5_7
  · fin_cases v
    · exact s214_6_0
    · exact s214_6_1
    · exact s214_6_2
    · exact s214_6_3
    · exact s214_6_4
    · exact s214_6_5
    · exact s214_6_6
    · exact s214_6_7
  · exact List.all_eq_true.mp col214_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
