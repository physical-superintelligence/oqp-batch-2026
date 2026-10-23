module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [230, 231). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col230_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 0 v) = true := by decide +kernel
theorem col230_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 1 v) = true := by decide +kernel
theorem col230_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 2 v) = true := by decide +kernel
theorem s230_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 0 = true := by decide +kernel
theorem s230_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 1 = true := by decide +kernel
theorem s230_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 2 = true := by decide +kernel
theorem k230_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k230_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k230_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s230_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k230_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k230_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 3 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k230_3_3_26 k h.1 (by omega)
theorem s230_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 4 = true := by decide +kernel
theorem s230_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 5 = true := by decide +kernel
theorem k230_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k230_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k230_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k230_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k230_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k230_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k230_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k230_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k230_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k230_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k230_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s230_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k230_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k230_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k230_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k230_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k230_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k230_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k230_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k230_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k230_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k230_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k230_3_6_130 k h.1 (by omega)
theorem s230_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 3 7 = true := by decide +kernel
theorem s230_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 0 = true := by decide +kernel
theorem s230_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 1 = true := by decide +kernel
theorem s230_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 2 = true := by decide +kernel
theorem s230_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 3 = true := by decide +kernel
theorem s230_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 4 = true := by decide +kernel
theorem s230_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 5 = true := by decide +kernel
theorem k230_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k230_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k230_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k230_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k230_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k230_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k230_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s230_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k230_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k230_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k230_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k230_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k230_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k230_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k230_4_6_126 k h.1 (by omega)
theorem s230_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 4 7 = true := by decide +kernel
theorem s230_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 0 = true := by decide +kernel
theorem s230_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 1 = true := by decide +kernel
theorem s230_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 2 = true := by decide +kernel
theorem s230_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 3 = true := by decide +kernel
theorem s230_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 4 = true := by decide +kernel
theorem s230_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 5 = true := by decide +kernel
theorem k230_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k230_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k230_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k230_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k230_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k230_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k230_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s230_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k230_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k230_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k230_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k230_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k230_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k230_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k230_5_6_126 k h.1 (by omega)
theorem s230_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 5 7 = true := by decide +kernel
theorem s230_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 0 = true := by decide +kernel
theorem s230_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 1 = true := by decide +kernel
theorem s230_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 2 = true := by decide +kernel
theorem k230_6_3_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k230_6_3_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k230_6_3_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k230_6_3_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k230_6_3_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k230_6_3_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k230_6_3_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k230_6_3_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k230_6_3_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k230_6_3_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k230_6_3_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k230_6_3_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem s230_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36)) with h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 0 3 k230_6_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 3 3 k230_6_3_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 6 3 k230_6_3_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 9 3 k230_6_3_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 12 3 k230_6_3_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 15 3 k230_6_3_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 18 3 k230_6_3_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 21 3 k230_6_3_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 24 3 k230_6_3_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 27 3 k230_6_3_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 30 3 k230_6_3_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 3 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 3) (x2SOff 1 6) (nS 1 6)) 33 3 k230_6_3_33 k h.1 (by omega)
theorem k230_6_4_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k230_6_4_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k230_6_4_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k230_6_4_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k230_6_4_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k230_6_4_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k230_6_4_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s230_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 4 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 4 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 0 3 k230_6_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 3 3 k230_6_4_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 6 3 k230_6_4_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 9 3 k230_6_4_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 12 3 k230_6_4_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 15 3 k230_6_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 4 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 4) (x2SOff 1 6) (nS 1 6)) 18 3 k230_6_4_18 k h.1 (by omega)
theorem k230_6_5_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k230_6_5_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k230_6_5_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k230_6_5_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k230_6_5_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k230_6_5_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k230_6_5_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem s230_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 5 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 5 = 21 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 0 3 k230_6_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 3 3 k230_6_5_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 6 3 k230_6_5_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 9 3 k230_6_5_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 12 3 k230_6_5_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 15 3 k230_6_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 5 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 5) (x2SOff 1 6) (nS 1 6)) 18 3 k230_6_5_18 k h.1 (by omega)
theorem k230_6_6_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k230_6_6_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k230_6_6_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k230_6_6_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k230_6_6_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem k230_6_6_15 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (15 + k)) = true := by decide +kernel
theorem k230_6_6_18 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (18 + k)) = true := by decide +kernel
theorem k230_6_6_21 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (21 + k)) = true := by decide +kernel
theorem k230_6_6_24 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (24 + k)) = true := by decide +kernel
theorem k230_6_6_27 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (27 + k)) = true := by decide +kernel
theorem k230_6_6_30 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (30 + k)) = true := by decide +kernel
theorem k230_6_6_33 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (33 + k)) = true := by decide +kernel
theorem k230_6_6_36 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (36 + k)) = true := by decide +kernel
theorem k230_6_6_39 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (39 + k)) = true := by decide +kernel
theorem k230_6_6_42 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (42 + k)) = true := by decide +kernel
theorem k230_6_6_45 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (45 + k)) = true := by decide +kernel
theorem k230_6_6_48 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (48 + k)) = true := by decide +kernel
theorem k230_6_6_51 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (51 + k)) = true := by decide +kernel
theorem k230_6_6_54 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (54 + k)) = true := by decide +kernel
theorem k230_6_6_57 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (57 + k)) = true := by decide +kernel
theorem k230_6_6_60 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (60 + k)) = true := by decide +kernel
theorem k230_6_6_63 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (63 + k)) = true := by decide +kernel
theorem k230_6_6_66 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (66 + k)) = true := by decide +kernel
theorem k230_6_6_69 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (69 + k)) = true := by decide +kernel
theorem k230_6_6_72 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (72 + k)) = true := by decide +kernel
theorem k230_6_6_75 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (75 + k)) = true := by decide +kernel
theorem k230_6_6_78 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (78 + k)) = true := by decide +kernel
theorem k230_6_6_81 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (81 + k)) = true := by decide +kernel
theorem k230_6_6_84 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (84 + k)) = true := by decide +kernel
theorem k230_6_6_87 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (87 + k)) = true := by decide +kernel
theorem k230_6_6_90 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (90 + k)) = true := by decide +kernel
theorem k230_6_6_93 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (93 + k)) = true := by decide +kernel
theorem k230_6_6_96 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (96 + k)) = true := by decide +kernel
theorem k230_6_6_99 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (99 + k)) = true := by decide +kernel
theorem k230_6_6_102 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (102 + k)) = true := by decide +kernel
theorem k230_6_6_105 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (105 + k)) = true := by decide +kernel
theorem k230_6_6_108 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (108 + k)) = true := by decide +kernel
theorem k230_6_6_111 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (111 + k)) = true := by decide +kernel
theorem k230_6_6_114 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (114 + k)) = true := by decide +kernel
theorem k230_6_6_117 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (117 + k)) = true := by decide +kernel
theorem k230_6_6_120 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (120 + k)) = true := by decide +kernel
theorem k230_6_6_123 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (123 + k)) = true := by decide +kernel
theorem k230_6_6_126 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (126 + k)) = true := by decide +kernel
theorem k230_6_6_129 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (129 + k)) = true := by decide +kernel
theorem k230_6_6_132 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (132 + k)) = true := by decide +kernel
theorem k230_6_6_135 : (List.range 1).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) (135 + k)) = true := by decide +kernel
theorem s230_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 6 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 18) ∨ (18 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 27) ∨ (27 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 33) ∨ (33 ≤ k ∧ k < 36) ∨ (36 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 51) ∨ (51 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 57) ∨ (57 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 66) ∨ (66 ≤ k ∧ k < 69) ∨ (69 ≤ k ∧ k < 72) ∨ (72 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 81) ∨ (81 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 87) ∨ (87 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 93) ∨ (93 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 99) ∨ (99 ≤ k ∧ k < 102) ∨ (102 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 108) ∨ (108 ≤ k ∧ k < 111) ∨ (111 ≤ k ∧ k < 114) ∨ (114 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 123) ∨ (123 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 129) ∨ (129 ≤ k ∧ k < 132) ∨ (132 ≤ k ∧ k < 135) ∨ (135 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 0 3 k230_6_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 3 3 k230_6_6_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 6 3 k230_6_6_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 9 3 k230_6_6_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 12 3 k230_6_6_12 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 15 3 k230_6_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 18 3 k230_6_6_18 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 21 3 k230_6_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 24 3 k230_6_6_24 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 27 3 k230_6_6_27 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 30 3 k230_6_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 33 3 k230_6_6_33 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 36 3 k230_6_6_36 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 39 3 k230_6_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 42 3 k230_6_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 45 3 k230_6_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 48 3 k230_6_6_48 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 51 3 k230_6_6_51 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 54 3 k230_6_6_54 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 57 3 k230_6_6_57 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 60 3 k230_6_6_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 63 3 k230_6_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 66 3 k230_6_6_66 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 69 3 k230_6_6_69 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 72 3 k230_6_6_72 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 75 3 k230_6_6_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 78 3 k230_6_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 81 3 k230_6_6_81 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 84 3 k230_6_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 87 3 k230_6_6_87 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 90 3 k230_6_6_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 93 3 k230_6_6_93 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 96 3 k230_6_6_96 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 99 3 k230_6_6_99 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 102 3 k230_6_6_102 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 105 3 k230_6_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 108 3 k230_6_6_108 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 111 3 k230_6_6_111 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 114 3 k230_6_6_114 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 117 3 k230_6_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 120 3 k230_6_6_120 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 123 3 k230_6_6_123 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 126 3 k230_6_6_126 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 129 3 k230_6_6_129 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 132 3 k230_6_6_132 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TCasaD 6 6 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 6) (x2SOff 1 6) (nS 1 6)) 135 1 k230_6_6_135 k h.1 (by omega)
theorem k230_6_7_0 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k230_6_7_3 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k230_6_7_6 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k230_6_7_9 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k230_6_7_12 : (List.range 3).all (fun k => (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s230_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 7 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 6 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k230_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k230_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k230_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k230_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 230) (InDA1.TTsaaD 6 7 7) (posA (x2Mult 1 7) (230 - x2AOff 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k230_6_7_12 k h.1 (by omega)
theorem col230_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 7 v) = true := by decide +kernel
theorem col230 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 230) 230 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col230_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col230_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col230_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s230_3_0
    · exact s230_3_1
    · exact s230_3_2
    · exact s230_3_3
    · exact s230_3_4
    · exact s230_3_5
    · exact s230_3_6
    · exact s230_3_7
  · fin_cases v
    · exact s230_4_0
    · exact s230_4_1
    · exact s230_4_2
    · exact s230_4_3
    · exact s230_4_4
    · exact s230_4_5
    · exact s230_4_6
    · exact s230_4_7
  · fin_cases v
    · exact s230_5_0
    · exact s230_5_1
    · exact s230_5_2
    · exact s230_5_3
    · exact s230_5_4
    · exact s230_5_5
    · exact s230_5_6
    · exact s230_5_7
  · fin_cases v
    · exact s230_6_0
    · exact s230_6_1
    · exact s230_6_2
    · exact s230_6_3
    · exact s230_6_4
    · exact s230_6_5
    · exact s230_6_6
    · exact s230_6_7
  · exact List.all_eq_true.mp col230_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
