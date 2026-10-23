module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [100, 105). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col100_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 0 v) = true := by decide +kernel
theorem col100_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 1 v) = true := by decide +kernel
theorem col100_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 2 v) = true := by decide +kernel
theorem s100_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 0 = true := by decide +kernel
theorem s100_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 1 = true := by decide +kernel
theorem s100_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 2 = true := by decide +kernel
theorem k100_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k100_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k100_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s100_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k100_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k100_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k100_3_3_26 k h.1 (by omega)
theorem s100_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 4 = true := by decide +kernel
theorem s100_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 5 = true := by decide +kernel
theorem k100_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k100_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k100_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k100_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k100_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k100_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k100_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k100_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k100_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k100_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k100_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s100_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k100_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k100_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k100_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k100_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k100_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k100_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k100_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k100_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k100_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k100_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k100_3_6_130 k h.1 (by omega)
theorem s100_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 3 7 = true := by decide +kernel
theorem s100_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 0 = true := by decide +kernel
theorem s100_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 1 = true := by decide +kernel
theorem s100_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 2 = true := by decide +kernel
theorem s100_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 3 = true := by decide +kernel
theorem s100_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 4 = true := by decide +kernel
theorem s100_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 5 = true := by decide +kernel
theorem k100_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k100_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k100_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k100_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k100_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k100_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k100_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s100_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k100_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k100_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k100_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k100_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k100_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k100_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k100_4_6_126 k h.1 (by omega)
theorem s100_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 4 7 = true := by decide +kernel
theorem s100_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 0 = true := by decide +kernel
theorem s100_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 1 = true := by decide +kernel
theorem s100_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 2 = true := by decide +kernel
theorem s100_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 3 = true := by decide +kernel
theorem s100_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 4 = true := by decide +kernel
theorem s100_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 5 = true := by decide +kernel
theorem k100_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k100_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k100_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k100_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k100_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k100_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k100_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s100_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k100_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k100_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k100_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k100_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k100_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k100_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 100) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (100 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k100_5_6_126 k h.1 (by omega)
theorem s100_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 5 7 = true := by decide +kernel
theorem s100_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 0 = true := by decide +kernel
theorem s100_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 1 = true := by decide +kernel
theorem s100_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 2 = true := by decide +kernel
theorem s100_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 3 = true := by decide +kernel
theorem s100_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 4 = true := by decide +kernel
theorem s100_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 5 = true := by decide +kernel
theorem s100_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 6 = true := by decide +kernel
theorem k100_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k100_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k100_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k100_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k100_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s100_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k100_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k100_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k100_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k100_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 100) ((InDA1.TCasaD 6 6 7).getD (100 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k100_6_7_12 k h.1 (by omega)
theorem col100_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 7 v) = true := by decide +kernel
theorem col100 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 100) 100 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col100_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col100_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col100_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s100_3_0
    · exact s100_3_1
    · exact s100_3_2
    · exact s100_3_3
    · exact s100_3_4
    · exact s100_3_5
    · exact s100_3_6
    · exact s100_3_7
  · fin_cases v
    · exact s100_4_0
    · exact s100_4_1
    · exact s100_4_2
    · exact s100_4_3
    · exact s100_4_4
    · exact s100_4_5
    · exact s100_4_6
    · exact s100_4_7
  · fin_cases v
    · exact s100_5_0
    · exact s100_5_1
    · exact s100_5_2
    · exact s100_5_3
    · exact s100_5_4
    · exact s100_5_5
    · exact s100_5_6
    · exact s100_5_7
  · fin_cases v
    · exact s100_6_0
    · exact s100_6_1
    · exact s100_6_2
    · exact s100_6_3
    · exact s100_6_4
    · exact s100_6_5
    · exact s100_6_6
    · exact s100_6_7
  · exact List.all_eq_true.mp col100_7 v (List.mem_finRange v)
theorem col101_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 0 v) = true := by decide +kernel
theorem col101_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 1 v) = true := by decide +kernel
theorem col101_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 2 v) = true := by decide +kernel
theorem s101_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 0 = true := by decide +kernel
theorem s101_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 1 = true := by decide +kernel
theorem s101_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 2 = true := by decide +kernel
theorem k101_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k101_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k101_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s101_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k101_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k101_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k101_3_3_26 k h.1 (by omega)
theorem s101_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 4 = true := by decide +kernel
theorem s101_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 5 = true := by decide +kernel
theorem k101_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k101_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k101_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k101_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k101_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k101_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k101_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k101_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k101_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k101_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k101_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s101_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k101_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k101_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k101_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k101_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k101_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k101_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k101_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k101_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k101_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k101_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k101_3_6_130 k h.1 (by omega)
theorem s101_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 3 7 = true := by decide +kernel
theorem s101_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 0 = true := by decide +kernel
theorem s101_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 1 = true := by decide +kernel
theorem s101_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 2 = true := by decide +kernel
theorem s101_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 3 = true := by decide +kernel
theorem s101_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 4 = true := by decide +kernel
theorem s101_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 5 = true := by decide +kernel
theorem k101_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k101_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k101_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k101_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k101_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k101_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k101_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s101_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k101_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k101_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k101_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k101_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k101_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k101_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k101_4_6_126 k h.1 (by omega)
theorem s101_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 4 7 = true := by decide +kernel
theorem s101_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 0 = true := by decide +kernel
theorem s101_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 1 = true := by decide +kernel
theorem s101_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 2 = true := by decide +kernel
theorem s101_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 3 = true := by decide +kernel
theorem s101_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 4 = true := by decide +kernel
theorem s101_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 5 = true := by decide +kernel
theorem k101_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k101_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k101_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k101_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k101_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k101_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k101_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s101_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k101_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k101_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k101_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k101_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k101_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k101_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 101) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (101 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k101_5_6_126 k h.1 (by omega)
theorem s101_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 5 7 = true := by decide +kernel
theorem s101_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 0 = true := by decide +kernel
theorem s101_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 1 = true := by decide +kernel
theorem s101_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 2 = true := by decide +kernel
theorem s101_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 3 = true := by decide +kernel
theorem s101_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 4 = true := by decide +kernel
theorem s101_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 5 = true := by decide +kernel
theorem s101_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 6 = true := by decide +kernel
theorem k101_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k101_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k101_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k101_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k101_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s101_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k101_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k101_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k101_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k101_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 101) ((InDA1.TCasaD 6 6 7).getD (101 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k101_6_7_12 k h.1 (by omega)
theorem col101_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 7 v) = true := by decide +kernel
theorem col101 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 101) 101 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col101_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col101_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col101_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s101_3_0
    · exact s101_3_1
    · exact s101_3_2
    · exact s101_3_3
    · exact s101_3_4
    · exact s101_3_5
    · exact s101_3_6
    · exact s101_3_7
  · fin_cases v
    · exact s101_4_0
    · exact s101_4_1
    · exact s101_4_2
    · exact s101_4_3
    · exact s101_4_4
    · exact s101_4_5
    · exact s101_4_6
    · exact s101_4_7
  · fin_cases v
    · exact s101_5_0
    · exact s101_5_1
    · exact s101_5_2
    · exact s101_5_3
    · exact s101_5_4
    · exact s101_5_5
    · exact s101_5_6
    · exact s101_5_7
  · fin_cases v
    · exact s101_6_0
    · exact s101_6_1
    · exact s101_6_2
    · exact s101_6_3
    · exact s101_6_4
    · exact s101_6_5
    · exact s101_6_6
    · exact s101_6_7
  · exact List.all_eq_true.mp col101_7 v (List.mem_finRange v)
theorem col102_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 0 v) = true := by decide +kernel
theorem col102_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 1 v) = true := by decide +kernel
theorem col102_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 2 v) = true := by decide +kernel
theorem s102_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 0 = true := by decide +kernel
theorem s102_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 1 = true := by decide +kernel
theorem s102_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 2 = true := by decide +kernel
theorem k102_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k102_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k102_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s102_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k102_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k102_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k102_3_3_26 k h.1 (by omega)
theorem s102_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 4 = true := by decide +kernel
theorem s102_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 5 = true := by decide +kernel
theorem k102_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k102_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k102_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k102_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k102_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k102_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k102_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k102_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k102_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k102_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k102_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s102_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k102_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k102_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k102_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k102_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k102_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k102_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k102_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k102_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k102_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k102_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k102_3_6_130 k h.1 (by omega)
theorem s102_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 3 7 = true := by decide +kernel
theorem s102_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 0 = true := by decide +kernel
theorem s102_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 1 = true := by decide +kernel
theorem s102_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 2 = true := by decide +kernel
theorem s102_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 3 = true := by decide +kernel
theorem s102_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 4 = true := by decide +kernel
theorem s102_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 5 = true := by decide +kernel
theorem k102_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k102_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k102_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k102_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k102_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k102_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k102_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s102_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k102_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k102_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k102_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k102_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k102_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k102_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k102_4_6_126 k h.1 (by omega)
theorem s102_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 4 7 = true := by decide +kernel
theorem s102_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 0 = true := by decide +kernel
theorem s102_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 1 = true := by decide +kernel
theorem s102_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 2 = true := by decide +kernel
theorem s102_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 3 = true := by decide +kernel
theorem s102_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 4 = true := by decide +kernel
theorem s102_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 5 = true := by decide +kernel
theorem k102_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k102_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k102_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k102_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k102_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k102_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k102_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s102_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k102_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k102_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k102_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k102_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k102_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k102_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 102) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (102 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k102_5_6_126 k h.1 (by omega)
theorem s102_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 5 7 = true := by decide +kernel
theorem s102_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 0 = true := by decide +kernel
theorem s102_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 1 = true := by decide +kernel
theorem s102_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 2 = true := by decide +kernel
theorem s102_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 3 = true := by decide +kernel
theorem s102_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 4 = true := by decide +kernel
theorem s102_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 5 = true := by decide +kernel
theorem s102_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 6 = true := by decide +kernel
theorem k102_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k102_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k102_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k102_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k102_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s102_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k102_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k102_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k102_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k102_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 102) ((InDA1.TCasaD 6 6 7).getD (102 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k102_6_7_12 k h.1 (by omega)
theorem col102_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 7 v) = true := by decide +kernel
theorem col102 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 102) 102 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col102_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col102_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col102_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s102_3_0
    · exact s102_3_1
    · exact s102_3_2
    · exact s102_3_3
    · exact s102_3_4
    · exact s102_3_5
    · exact s102_3_6
    · exact s102_3_7
  · fin_cases v
    · exact s102_4_0
    · exact s102_4_1
    · exact s102_4_2
    · exact s102_4_3
    · exact s102_4_4
    · exact s102_4_5
    · exact s102_4_6
    · exact s102_4_7
  · fin_cases v
    · exact s102_5_0
    · exact s102_5_1
    · exact s102_5_2
    · exact s102_5_3
    · exact s102_5_4
    · exact s102_5_5
    · exact s102_5_6
    · exact s102_5_7
  · fin_cases v
    · exact s102_6_0
    · exact s102_6_1
    · exact s102_6_2
    · exact s102_6_3
    · exact s102_6_4
    · exact s102_6_5
    · exact s102_6_6
    · exact s102_6_7
  · exact List.all_eq_true.mp col102_7 v (List.mem_finRange v)
theorem col103_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 0 v) = true := by decide +kernel
theorem col103_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 1 v) = true := by decide +kernel
theorem col103_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 2 v) = true := by decide +kernel
theorem s103_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 0 = true := by decide +kernel
theorem s103_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 1 = true := by decide +kernel
theorem s103_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 2 = true := by decide +kernel
theorem k103_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k103_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k103_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s103_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k103_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k103_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k103_3_3_26 k h.1 (by omega)
theorem s103_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 4 = true := by decide +kernel
theorem s103_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 5 = true := by decide +kernel
theorem k103_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k103_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k103_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k103_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k103_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k103_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k103_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k103_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k103_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k103_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k103_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s103_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k103_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k103_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k103_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k103_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k103_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k103_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k103_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k103_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k103_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k103_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k103_3_6_130 k h.1 (by omega)
theorem s103_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 3 7 = true := by decide +kernel
theorem s103_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 0 = true := by decide +kernel
theorem s103_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 1 = true := by decide +kernel
theorem s103_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 2 = true := by decide +kernel
theorem s103_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 3 = true := by decide +kernel
theorem s103_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 4 = true := by decide +kernel
theorem s103_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 5 = true := by decide +kernel
theorem k103_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k103_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k103_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k103_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k103_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k103_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k103_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s103_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k103_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k103_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k103_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k103_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k103_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k103_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k103_4_6_126 k h.1 (by omega)
theorem s103_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 4 7 = true := by decide +kernel
theorem s103_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 0 = true := by decide +kernel
theorem s103_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 1 = true := by decide +kernel
theorem s103_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 2 = true := by decide +kernel
theorem s103_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 3 = true := by decide +kernel
theorem s103_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 4 = true := by decide +kernel
theorem s103_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 5 = true := by decide +kernel
theorem k103_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k103_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k103_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k103_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k103_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k103_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k103_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s103_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k103_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k103_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k103_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k103_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k103_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k103_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 103) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (103 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k103_5_6_126 k h.1 (by omega)
theorem s103_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 5 7 = true := by decide +kernel
theorem s103_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 0 = true := by decide +kernel
theorem s103_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 1 = true := by decide +kernel
theorem s103_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 2 = true := by decide +kernel
theorem s103_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 3 = true := by decide +kernel
theorem s103_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 4 = true := by decide +kernel
theorem s103_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 5 = true := by decide +kernel
theorem s103_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 6 = true := by decide +kernel
theorem k103_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k103_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k103_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k103_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k103_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s103_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k103_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k103_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k103_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k103_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 103) ((InDA1.TCasaD 6 6 7).getD (103 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k103_6_7_12 k h.1 (by omega)
theorem col103_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 7 v) = true := by decide +kernel
theorem col103 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 103) 103 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col103_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col103_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col103_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s103_3_0
    · exact s103_3_1
    · exact s103_3_2
    · exact s103_3_3
    · exact s103_3_4
    · exact s103_3_5
    · exact s103_3_6
    · exact s103_3_7
  · fin_cases v
    · exact s103_4_0
    · exact s103_4_1
    · exact s103_4_2
    · exact s103_4_3
    · exact s103_4_4
    · exact s103_4_5
    · exact s103_4_6
    · exact s103_4_7
  · fin_cases v
    · exact s103_5_0
    · exact s103_5_1
    · exact s103_5_2
    · exact s103_5_3
    · exact s103_5_4
    · exact s103_5_5
    · exact s103_5_6
    · exact s103_5_7
  · fin_cases v
    · exact s103_6_0
    · exact s103_6_1
    · exact s103_6_2
    · exact s103_6_3
    · exact s103_6_4
    · exact s103_6_5
    · exact s103_6_6
    · exact s103_6_7
  · exact List.all_eq_true.mp col103_7 v (List.mem_finRange v)
theorem col104_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 0 v) = true := by decide +kernel
theorem col104_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 1 v) = true := by decide +kernel
theorem col104_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 2 v) = true := by decide +kernel
theorem s104_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 0 = true := by decide +kernel
theorem s104_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 1 = true := by decide +kernel
theorem s104_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 2 = true := by decide +kernel
theorem k104_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k104_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k104_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s104_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k104_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k104_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k104_3_3_26 k h.1 (by omega)
theorem s104_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 4 = true := by decide +kernel
theorem s104_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 5 = true := by decide +kernel
theorem k104_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k104_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k104_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k104_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k104_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k104_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k104_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k104_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k104_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k104_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k104_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s104_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k104_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k104_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k104_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k104_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k104_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k104_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k104_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k104_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k104_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k104_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k104_3_6_130 k h.1 (by omega)
theorem s104_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 3 7 = true := by decide +kernel
theorem s104_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 0 = true := by decide +kernel
theorem s104_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 1 = true := by decide +kernel
theorem s104_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 2 = true := by decide +kernel
theorem s104_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 3 = true := by decide +kernel
theorem s104_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 4 = true := by decide +kernel
theorem s104_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 5 = true := by decide +kernel
theorem k104_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k104_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k104_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k104_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k104_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k104_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k104_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s104_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k104_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k104_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k104_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k104_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k104_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k104_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k104_4_6_126 k h.1 (by omega)
theorem s104_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 4 7 = true := by decide +kernel
theorem s104_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 0 = true := by decide +kernel
theorem s104_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 1 = true := by decide +kernel
theorem s104_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 2 = true := by decide +kernel
theorem s104_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 3 = true := by decide +kernel
theorem s104_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 4 = true := by decide +kernel
theorem s104_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 5 = true := by decide +kernel
theorem k104_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k104_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k104_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k104_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k104_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k104_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k104_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s104_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k104_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k104_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k104_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k104_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k104_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k104_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 104) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (104 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k104_5_6_126 k h.1 (by omega)
theorem s104_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 5 7 = true := by decide +kernel
theorem s104_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 0 = true := by decide +kernel
theorem s104_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 1 = true := by decide +kernel
theorem s104_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 2 = true := by decide +kernel
theorem s104_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 3 = true := by decide +kernel
theorem s104_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 4 = true := by decide +kernel
theorem s104_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 5 = true := by decide +kernel
theorem s104_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 6 = true := by decide +kernel
theorem k104_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k104_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k104_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k104_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k104_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s104_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k104_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k104_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k104_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k104_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 104) ((InDA1.TCasaD 6 6 7).getD (104 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k104_6_7_12 k h.1 (by omega)
theorem col104_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 7 v) = true := by decide +kernel
theorem col104 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 104) 104 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col104_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col104_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col104_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s104_3_0
    · exact s104_3_1
    · exact s104_3_2
    · exact s104_3_3
    · exact s104_3_4
    · exact s104_3_5
    · exact s104_3_6
    · exact s104_3_7
  · fin_cases v
    · exact s104_4_0
    · exact s104_4_1
    · exact s104_4_2
    · exact s104_4_3
    · exact s104_4_4
    · exact s104_4_5
    · exact s104_4_6
    · exact s104_4_7
  · fin_cases v
    · exact s104_5_0
    · exact s104_5_1
    · exact s104_5_2
    · exact s104_5_3
    · exact s104_5_4
    · exact s104_5_5
    · exact s104_5_6
    · exact s104_5_7
  · fin_cases v
    · exact s104_6_0
    · exact s104_6_1
    · exact s104_6_2
    · exact s104_6_3
    · exact s104_6_4
    · exact s104_6_5
    · exact s104_6_6
    · exact s104_6_7
  · exact List.all_eq_true.mp col104_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
