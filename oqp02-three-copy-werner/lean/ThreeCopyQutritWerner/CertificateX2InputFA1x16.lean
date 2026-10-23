module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [80, 85). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col80_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 0 v) = true := by decide +kernel
theorem col80_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 1 v) = true := by decide +kernel
theorem col80_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 2 v) = true := by decide +kernel
theorem s80_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 0 = true := by decide +kernel
theorem s80_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 1 = true := by decide +kernel
theorem s80_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 2 = true := by decide +kernel
theorem k80_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k80_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k80_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s80_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k80_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k80_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k80_3_3_26 k h.1 (by omega)
theorem s80_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 4 = true := by decide +kernel
theorem s80_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 5 = true := by decide +kernel
theorem k80_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k80_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k80_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k80_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k80_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k80_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k80_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k80_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k80_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k80_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k80_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s80_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k80_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k80_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k80_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k80_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k80_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k80_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k80_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k80_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k80_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k80_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k80_3_6_130 k h.1 (by omega)
theorem s80_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 3 7 = true := by decide +kernel
theorem s80_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 0 = true := by decide +kernel
theorem s80_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 1 = true := by decide +kernel
theorem s80_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 2 = true := by decide +kernel
theorem s80_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 3 = true := by decide +kernel
theorem s80_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 4 = true := by decide +kernel
theorem s80_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 5 = true := by decide +kernel
theorem k80_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k80_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k80_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k80_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k80_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k80_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k80_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s80_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k80_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k80_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k80_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k80_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k80_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k80_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k80_4_6_126 k h.1 (by omega)
theorem s80_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 4 7 = true := by decide +kernel
theorem s80_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 0 = true := by decide +kernel
theorem s80_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 1 = true := by decide +kernel
theorem s80_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 2 = true := by decide +kernel
theorem s80_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 3 = true := by decide +kernel
theorem s80_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 4 = true := by decide +kernel
theorem s80_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 5 = true := by decide +kernel
theorem k80_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k80_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k80_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k80_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k80_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k80_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k80_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s80_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k80_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k80_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k80_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k80_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k80_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k80_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 80) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (80 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k80_5_6_126 k h.1 (by omega)
theorem s80_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 5 7 = true := by decide +kernel
theorem s80_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 0 = true := by decide +kernel
theorem s80_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 1 = true := by decide +kernel
theorem s80_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 2 = true := by decide +kernel
theorem s80_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 3 = true := by decide +kernel
theorem s80_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 4 = true := by decide +kernel
theorem s80_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 5 = true := by decide +kernel
theorem s80_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 6 = true := by decide +kernel
theorem k80_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k80_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k80_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k80_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k80_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s80_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k80_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k80_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k80_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k80_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 80) ((InDA1.TCasaD 6 6 7).getD (80 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k80_6_7_12 k h.1 (by omega)
theorem col80_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 7 v) = true := by decide +kernel
theorem col80 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 80) 80 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col80_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col80_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col80_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s80_3_0
    · exact s80_3_1
    · exact s80_3_2
    · exact s80_3_3
    · exact s80_3_4
    · exact s80_3_5
    · exact s80_3_6
    · exact s80_3_7
  · fin_cases v
    · exact s80_4_0
    · exact s80_4_1
    · exact s80_4_2
    · exact s80_4_3
    · exact s80_4_4
    · exact s80_4_5
    · exact s80_4_6
    · exact s80_4_7
  · fin_cases v
    · exact s80_5_0
    · exact s80_5_1
    · exact s80_5_2
    · exact s80_5_3
    · exact s80_5_4
    · exact s80_5_5
    · exact s80_5_6
    · exact s80_5_7
  · fin_cases v
    · exact s80_6_0
    · exact s80_6_1
    · exact s80_6_2
    · exact s80_6_3
    · exact s80_6_4
    · exact s80_6_5
    · exact s80_6_6
    · exact s80_6_7
  · exact List.all_eq_true.mp col80_7 v (List.mem_finRange v)
theorem col81_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 0 v) = true := by decide +kernel
theorem col81_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 1 v) = true := by decide +kernel
theorem col81_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 2 v) = true := by decide +kernel
theorem s81_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 0 = true := by decide +kernel
theorem s81_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 1 = true := by decide +kernel
theorem s81_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 2 = true := by decide +kernel
theorem k81_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k81_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k81_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s81_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k81_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k81_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k81_3_3_26 k h.1 (by omega)
theorem s81_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 4 = true := by decide +kernel
theorem s81_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 5 = true := by decide +kernel
theorem k81_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k81_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k81_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k81_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k81_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k81_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k81_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k81_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k81_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k81_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k81_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s81_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k81_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k81_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k81_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k81_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k81_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k81_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k81_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k81_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k81_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k81_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k81_3_6_130 k h.1 (by omega)
theorem s81_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 3 7 = true := by decide +kernel
theorem s81_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 0 = true := by decide +kernel
theorem s81_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 1 = true := by decide +kernel
theorem s81_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 2 = true := by decide +kernel
theorem s81_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 3 = true := by decide +kernel
theorem s81_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 4 = true := by decide +kernel
theorem s81_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 5 = true := by decide +kernel
theorem k81_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k81_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k81_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k81_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k81_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k81_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k81_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s81_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k81_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k81_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k81_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k81_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k81_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k81_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k81_4_6_126 k h.1 (by omega)
theorem s81_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 4 7 = true := by decide +kernel
theorem s81_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 0 = true := by decide +kernel
theorem s81_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 1 = true := by decide +kernel
theorem s81_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 2 = true := by decide +kernel
theorem s81_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 3 = true := by decide +kernel
theorem s81_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 4 = true := by decide +kernel
theorem s81_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 5 = true := by decide +kernel
theorem k81_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k81_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k81_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k81_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k81_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k81_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k81_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s81_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k81_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k81_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k81_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k81_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k81_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k81_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 81) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (81 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k81_5_6_126 k h.1 (by omega)
theorem s81_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 5 7 = true := by decide +kernel
theorem s81_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 0 = true := by decide +kernel
theorem s81_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 1 = true := by decide +kernel
theorem s81_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 2 = true := by decide +kernel
theorem s81_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 3 = true := by decide +kernel
theorem s81_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 4 = true := by decide +kernel
theorem s81_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 5 = true := by decide +kernel
theorem s81_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 6 = true := by decide +kernel
theorem k81_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k81_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k81_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k81_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k81_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s81_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k81_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k81_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k81_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k81_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 81) ((InDA1.TCasaD 6 6 7).getD (81 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k81_6_7_12 k h.1 (by omega)
theorem col81_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 7 v) = true := by decide +kernel
theorem col81 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 81) 81 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col81_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col81_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col81_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s81_3_0
    · exact s81_3_1
    · exact s81_3_2
    · exact s81_3_3
    · exact s81_3_4
    · exact s81_3_5
    · exact s81_3_6
    · exact s81_3_7
  · fin_cases v
    · exact s81_4_0
    · exact s81_4_1
    · exact s81_4_2
    · exact s81_4_3
    · exact s81_4_4
    · exact s81_4_5
    · exact s81_4_6
    · exact s81_4_7
  · fin_cases v
    · exact s81_5_0
    · exact s81_5_1
    · exact s81_5_2
    · exact s81_5_3
    · exact s81_5_4
    · exact s81_5_5
    · exact s81_5_6
    · exact s81_5_7
  · fin_cases v
    · exact s81_6_0
    · exact s81_6_1
    · exact s81_6_2
    · exact s81_6_3
    · exact s81_6_4
    · exact s81_6_5
    · exact s81_6_6
    · exact s81_6_7
  · exact List.all_eq_true.mp col81_7 v (List.mem_finRange v)
theorem col82_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 0 v) = true := by decide +kernel
theorem col82_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 1 v) = true := by decide +kernel
theorem col82_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 2 v) = true := by decide +kernel
theorem s82_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 0 = true := by decide +kernel
theorem s82_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 1 = true := by decide +kernel
theorem s82_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 2 = true := by decide +kernel
theorem k82_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k82_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k82_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s82_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k82_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k82_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k82_3_3_26 k h.1 (by omega)
theorem s82_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 4 = true := by decide +kernel
theorem s82_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 5 = true := by decide +kernel
theorem k82_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k82_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k82_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k82_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k82_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k82_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k82_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k82_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k82_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k82_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k82_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s82_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k82_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k82_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k82_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k82_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k82_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k82_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k82_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k82_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k82_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k82_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k82_3_6_130 k h.1 (by omega)
theorem s82_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 3 7 = true := by decide +kernel
theorem s82_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 0 = true := by decide +kernel
theorem s82_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 1 = true := by decide +kernel
theorem s82_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 2 = true := by decide +kernel
theorem s82_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 3 = true := by decide +kernel
theorem s82_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 4 = true := by decide +kernel
theorem s82_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 5 = true := by decide +kernel
theorem k82_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k82_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k82_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k82_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k82_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k82_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k82_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s82_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k82_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k82_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k82_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k82_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k82_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k82_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k82_4_6_126 k h.1 (by omega)
theorem s82_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 4 7 = true := by decide +kernel
theorem s82_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 0 = true := by decide +kernel
theorem s82_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 1 = true := by decide +kernel
theorem s82_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 2 = true := by decide +kernel
theorem s82_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 3 = true := by decide +kernel
theorem s82_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 4 = true := by decide +kernel
theorem s82_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 5 = true := by decide +kernel
theorem k82_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k82_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k82_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k82_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k82_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k82_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k82_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s82_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k82_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k82_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k82_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k82_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k82_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k82_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 82) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (82 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k82_5_6_126 k h.1 (by omega)
theorem s82_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 5 7 = true := by decide +kernel
theorem s82_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 0 = true := by decide +kernel
theorem s82_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 1 = true := by decide +kernel
theorem s82_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 2 = true := by decide +kernel
theorem s82_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 3 = true := by decide +kernel
theorem s82_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 4 = true := by decide +kernel
theorem s82_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 5 = true := by decide +kernel
theorem s82_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 6 = true := by decide +kernel
theorem k82_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k82_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k82_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k82_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k82_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s82_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k82_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k82_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k82_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k82_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 82) ((InDA1.TCasaD 6 6 7).getD (82 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k82_6_7_12 k h.1 (by omega)
theorem col82_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 7 v) = true := by decide +kernel
theorem col82 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 82) 82 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col82_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col82_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col82_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s82_3_0
    · exact s82_3_1
    · exact s82_3_2
    · exact s82_3_3
    · exact s82_3_4
    · exact s82_3_5
    · exact s82_3_6
    · exact s82_3_7
  · fin_cases v
    · exact s82_4_0
    · exact s82_4_1
    · exact s82_4_2
    · exact s82_4_3
    · exact s82_4_4
    · exact s82_4_5
    · exact s82_4_6
    · exact s82_4_7
  · fin_cases v
    · exact s82_5_0
    · exact s82_5_1
    · exact s82_5_2
    · exact s82_5_3
    · exact s82_5_4
    · exact s82_5_5
    · exact s82_5_6
    · exact s82_5_7
  · fin_cases v
    · exact s82_6_0
    · exact s82_6_1
    · exact s82_6_2
    · exact s82_6_3
    · exact s82_6_4
    · exact s82_6_5
    · exact s82_6_6
    · exact s82_6_7
  · exact List.all_eq_true.mp col82_7 v (List.mem_finRange v)
theorem col83_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 0 v) = true := by decide +kernel
theorem col83_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 1 v) = true := by decide +kernel
theorem col83_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 2 v) = true := by decide +kernel
theorem s83_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 0 = true := by decide +kernel
theorem s83_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 1 = true := by decide +kernel
theorem s83_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 2 = true := by decide +kernel
theorem k83_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k83_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k83_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s83_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k83_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k83_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k83_3_3_26 k h.1 (by omega)
theorem s83_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 4 = true := by decide +kernel
theorem s83_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 5 = true := by decide +kernel
theorem k83_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k83_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k83_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k83_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k83_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k83_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k83_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k83_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k83_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k83_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k83_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s83_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k83_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k83_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k83_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k83_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k83_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k83_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k83_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k83_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k83_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k83_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k83_3_6_130 k h.1 (by omega)
theorem s83_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 3 7 = true := by decide +kernel
theorem s83_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 0 = true := by decide +kernel
theorem s83_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 1 = true := by decide +kernel
theorem s83_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 2 = true := by decide +kernel
theorem s83_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 3 = true := by decide +kernel
theorem s83_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 4 = true := by decide +kernel
theorem s83_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 5 = true := by decide +kernel
theorem k83_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k83_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k83_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k83_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k83_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k83_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k83_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s83_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k83_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k83_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k83_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k83_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k83_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k83_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k83_4_6_126 k h.1 (by omega)
theorem s83_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 4 7 = true := by decide +kernel
theorem s83_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 0 = true := by decide +kernel
theorem s83_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 1 = true := by decide +kernel
theorem s83_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 2 = true := by decide +kernel
theorem s83_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 3 = true := by decide +kernel
theorem s83_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 4 = true := by decide +kernel
theorem s83_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 5 = true := by decide +kernel
theorem k83_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k83_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k83_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k83_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k83_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k83_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k83_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s83_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k83_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k83_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k83_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k83_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k83_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k83_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 83) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (83 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k83_5_6_126 k h.1 (by omega)
theorem s83_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 5 7 = true := by decide +kernel
theorem s83_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 0 = true := by decide +kernel
theorem s83_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 1 = true := by decide +kernel
theorem s83_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 2 = true := by decide +kernel
theorem s83_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 3 = true := by decide +kernel
theorem s83_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 4 = true := by decide +kernel
theorem s83_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 5 = true := by decide +kernel
theorem s83_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 6 = true := by decide +kernel
theorem k83_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k83_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k83_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k83_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k83_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s83_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k83_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k83_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k83_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k83_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 83) ((InDA1.TCasaD 6 6 7).getD (83 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k83_6_7_12 k h.1 (by omega)
theorem col83_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 7 v) = true := by decide +kernel
theorem col83 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 83) 83 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col83_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col83_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col83_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s83_3_0
    · exact s83_3_1
    · exact s83_3_2
    · exact s83_3_3
    · exact s83_3_4
    · exact s83_3_5
    · exact s83_3_6
    · exact s83_3_7
  · fin_cases v
    · exact s83_4_0
    · exact s83_4_1
    · exact s83_4_2
    · exact s83_4_3
    · exact s83_4_4
    · exact s83_4_5
    · exact s83_4_6
    · exact s83_4_7
  · fin_cases v
    · exact s83_5_0
    · exact s83_5_1
    · exact s83_5_2
    · exact s83_5_3
    · exact s83_5_4
    · exact s83_5_5
    · exact s83_5_6
    · exact s83_5_7
  · fin_cases v
    · exact s83_6_0
    · exact s83_6_1
    · exact s83_6_2
    · exact s83_6_3
    · exact s83_6_4
    · exact s83_6_5
    · exact s83_6_6
    · exact s83_6_7
  · exact List.all_eq_true.mp col83_7 v (List.mem_finRange v)
theorem col84_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 0 v) = true := by decide +kernel
theorem col84_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 1 v) = true := by decide +kernel
theorem col84_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 2 v) = true := by decide +kernel
theorem s84_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 0 = true := by decide +kernel
theorem s84_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 1 = true := by decide +kernel
theorem s84_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 2 = true := by decide +kernel
theorem k84_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k84_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k84_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s84_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k84_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k84_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k84_3_3_26 k h.1 (by omega)
theorem s84_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 4 = true := by decide +kernel
theorem s84_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 5 = true := by decide +kernel
theorem k84_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k84_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k84_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k84_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k84_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k84_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k84_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k84_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k84_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k84_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k84_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s84_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k84_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k84_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k84_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k84_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k84_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k84_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k84_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k84_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k84_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k84_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k84_3_6_130 k h.1 (by omega)
theorem s84_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 3 7 = true := by decide +kernel
theorem s84_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 0 = true := by decide +kernel
theorem s84_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 1 = true := by decide +kernel
theorem s84_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 2 = true := by decide +kernel
theorem s84_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 3 = true := by decide +kernel
theorem s84_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 4 = true := by decide +kernel
theorem s84_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 5 = true := by decide +kernel
theorem k84_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k84_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k84_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k84_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k84_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k84_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k84_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s84_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k84_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k84_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k84_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k84_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k84_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k84_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k84_4_6_126 k h.1 (by omega)
theorem s84_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 4 7 = true := by decide +kernel
theorem s84_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 0 = true := by decide +kernel
theorem s84_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 1 = true := by decide +kernel
theorem s84_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 2 = true := by decide +kernel
theorem s84_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 3 = true := by decide +kernel
theorem s84_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 4 = true := by decide +kernel
theorem s84_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 5 = true := by decide +kernel
theorem k84_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k84_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k84_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k84_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k84_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k84_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k84_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s84_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k84_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k84_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k84_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k84_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k84_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k84_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 84) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (84 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k84_5_6_126 k h.1 (by omega)
theorem s84_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 5 7 = true := by decide +kernel
theorem s84_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 0 = true := by decide +kernel
theorem s84_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 1 = true := by decide +kernel
theorem s84_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 2 = true := by decide +kernel
theorem s84_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 3 = true := by decide +kernel
theorem s84_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 4 = true := by decide +kernel
theorem s84_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 5 = true := by decide +kernel
theorem s84_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 6 = true := by decide +kernel
theorem k84_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k84_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k84_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k84_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k84_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s84_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k84_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k84_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k84_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k84_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 84) ((InDA1.TCasaD 6 6 7).getD (84 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k84_6_7_12 k h.1 (by omega)
theorem col84_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 7 v) = true := by decide +kernel
theorem col84 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 84) 84 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col84_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col84_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col84_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s84_3_0
    · exact s84_3_1
    · exact s84_3_2
    · exact s84_3_3
    · exact s84_3_4
    · exact s84_3_5
    · exact s84_3_6
    · exact s84_3_7
  · fin_cases v
    · exact s84_4_0
    · exact s84_4_1
    · exact s84_4_2
    · exact s84_4_3
    · exact s84_4_4
    · exact s84_4_5
    · exact s84_4_6
    · exact s84_4_7
  · fin_cases v
    · exact s84_5_0
    · exact s84_5_1
    · exact s84_5_2
    · exact s84_5_3
    · exact s84_5_4
    · exact s84_5_5
    · exact s84_5_6
    · exact s84_5_7
  · fin_cases v
    · exact s84_6_0
    · exact s84_6_1
    · exact s84_6_2
    · exact s84_6_3
    · exact s84_6_4
    · exact s84_6_5
    · exact s84_6_6
    · exact s84_6_7
  · exact List.all_eq_true.mp col84_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
