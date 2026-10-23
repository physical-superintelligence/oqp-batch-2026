module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [160, 165). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col160_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 0 v) = true := by decide +kernel
theorem col160_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 1 v) = true := by decide +kernel
theorem col160_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 2 v) = true := by decide +kernel
theorem s160_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 0 = true := by decide +kernel
theorem s160_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 1 = true := by decide +kernel
theorem s160_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 2 = true := by decide +kernel
theorem k160_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k160_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k160_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s160_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k160_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k160_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k160_3_3_26 k h.1 (by omega)
theorem s160_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 4 = true := by decide +kernel
theorem s160_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 5 = true := by decide +kernel
theorem k160_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k160_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k160_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k160_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k160_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k160_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k160_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k160_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k160_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k160_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k160_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s160_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k160_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k160_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k160_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k160_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k160_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k160_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k160_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k160_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k160_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k160_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k160_3_6_130 k h.1 (by omega)
theorem s160_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 3 7 = true := by decide +kernel
theorem s160_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 0 = true := by decide +kernel
theorem s160_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 1 = true := by decide +kernel
theorem s160_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 2 = true := by decide +kernel
theorem s160_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 3 = true := by decide +kernel
theorem s160_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 4 = true := by decide +kernel
theorem s160_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 5 = true := by decide +kernel
theorem k160_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k160_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k160_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k160_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k160_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k160_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k160_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s160_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k160_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k160_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k160_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k160_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k160_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k160_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k160_4_6_126 k h.1 (by omega)
theorem s160_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 4 7 = true := by decide +kernel
theorem s160_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 0 = true := by decide +kernel
theorem s160_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 1 = true := by decide +kernel
theorem s160_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 2 = true := by decide +kernel
theorem s160_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 3 = true := by decide +kernel
theorem s160_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 4 = true := by decide +kernel
theorem s160_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 5 = true := by decide +kernel
theorem k160_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k160_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k160_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k160_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k160_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k160_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k160_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s160_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k160_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k160_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k160_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k160_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k160_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k160_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 160) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (160 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k160_5_6_126 k h.1 (by omega)
theorem s160_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 5 7 = true := by decide +kernel
theorem s160_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 0 = true := by decide +kernel
theorem s160_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 1 = true := by decide +kernel
theorem s160_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 2 = true := by decide +kernel
theorem s160_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 3 = true := by decide +kernel
theorem s160_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 4 = true := by decide +kernel
theorem s160_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 5 = true := by decide +kernel
theorem s160_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 6 = true := by decide +kernel
theorem k160_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k160_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k160_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k160_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k160_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s160_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k160_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k160_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k160_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k160_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 160) ((InDA1.TCasaD 6 6 7).getD (160 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k160_6_7_12 k h.1 (by omega)
theorem col160_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 7 v) = true := by decide +kernel
theorem col160 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 160) 160 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col160_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col160_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col160_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s160_3_0
    · exact s160_3_1
    · exact s160_3_2
    · exact s160_3_3
    · exact s160_3_4
    · exact s160_3_5
    · exact s160_3_6
    · exact s160_3_7
  · fin_cases v
    · exact s160_4_0
    · exact s160_4_1
    · exact s160_4_2
    · exact s160_4_3
    · exact s160_4_4
    · exact s160_4_5
    · exact s160_4_6
    · exact s160_4_7
  · fin_cases v
    · exact s160_5_0
    · exact s160_5_1
    · exact s160_5_2
    · exact s160_5_3
    · exact s160_5_4
    · exact s160_5_5
    · exact s160_5_6
    · exact s160_5_7
  · fin_cases v
    · exact s160_6_0
    · exact s160_6_1
    · exact s160_6_2
    · exact s160_6_3
    · exact s160_6_4
    · exact s160_6_5
    · exact s160_6_6
    · exact s160_6_7
  · exact List.all_eq_true.mp col160_7 v (List.mem_finRange v)
theorem col161_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 0 v) = true := by decide +kernel
theorem col161_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 1 v) = true := by decide +kernel
theorem col161_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 2 v) = true := by decide +kernel
theorem s161_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 0 = true := by decide +kernel
theorem s161_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 1 = true := by decide +kernel
theorem s161_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 2 = true := by decide +kernel
theorem k161_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k161_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k161_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s161_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k161_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k161_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k161_3_3_26 k h.1 (by omega)
theorem s161_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 4 = true := by decide +kernel
theorem s161_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 5 = true := by decide +kernel
theorem k161_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k161_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k161_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k161_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k161_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k161_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k161_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k161_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k161_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k161_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k161_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s161_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k161_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k161_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k161_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k161_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k161_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k161_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k161_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k161_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k161_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k161_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k161_3_6_130 k h.1 (by omega)
theorem s161_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 3 7 = true := by decide +kernel
theorem s161_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 0 = true := by decide +kernel
theorem s161_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 1 = true := by decide +kernel
theorem s161_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 2 = true := by decide +kernel
theorem s161_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 3 = true := by decide +kernel
theorem s161_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 4 = true := by decide +kernel
theorem s161_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 5 = true := by decide +kernel
theorem k161_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k161_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k161_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k161_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k161_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k161_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k161_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s161_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k161_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k161_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k161_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k161_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k161_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k161_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k161_4_6_126 k h.1 (by omega)
theorem s161_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 4 7 = true := by decide +kernel
theorem s161_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 0 = true := by decide +kernel
theorem s161_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 1 = true := by decide +kernel
theorem s161_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 2 = true := by decide +kernel
theorem s161_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 3 = true := by decide +kernel
theorem s161_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 4 = true := by decide +kernel
theorem s161_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 5 = true := by decide +kernel
theorem k161_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k161_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k161_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k161_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k161_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k161_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k161_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s161_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k161_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k161_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k161_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k161_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k161_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k161_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 161) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (161 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k161_5_6_126 k h.1 (by omega)
theorem s161_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 5 7 = true := by decide +kernel
theorem s161_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 0 = true := by decide +kernel
theorem s161_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 1 = true := by decide +kernel
theorem s161_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 2 = true := by decide +kernel
theorem s161_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 3 = true := by decide +kernel
theorem s161_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 4 = true := by decide +kernel
theorem s161_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 5 = true := by decide +kernel
theorem s161_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 6 = true := by decide +kernel
theorem k161_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k161_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k161_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k161_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k161_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s161_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k161_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k161_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k161_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k161_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 161) ((InDA1.TCasaD 6 6 7).getD (161 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k161_6_7_12 k h.1 (by omega)
theorem col161_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 7 v) = true := by decide +kernel
theorem col161 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 161) 161 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col161_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col161_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col161_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s161_3_0
    · exact s161_3_1
    · exact s161_3_2
    · exact s161_3_3
    · exact s161_3_4
    · exact s161_3_5
    · exact s161_3_6
    · exact s161_3_7
  · fin_cases v
    · exact s161_4_0
    · exact s161_4_1
    · exact s161_4_2
    · exact s161_4_3
    · exact s161_4_4
    · exact s161_4_5
    · exact s161_4_6
    · exact s161_4_7
  · fin_cases v
    · exact s161_5_0
    · exact s161_5_1
    · exact s161_5_2
    · exact s161_5_3
    · exact s161_5_4
    · exact s161_5_5
    · exact s161_5_6
    · exact s161_5_7
  · fin_cases v
    · exact s161_6_0
    · exact s161_6_1
    · exact s161_6_2
    · exact s161_6_3
    · exact s161_6_4
    · exact s161_6_5
    · exact s161_6_6
    · exact s161_6_7
  · exact List.all_eq_true.mp col161_7 v (List.mem_finRange v)
theorem col162_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 0 v) = true := by decide +kernel
theorem col162_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 1 v) = true := by decide +kernel
theorem col162_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 2 v) = true := by decide +kernel
theorem s162_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 0 = true := by decide +kernel
theorem s162_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 1 = true := by decide +kernel
theorem s162_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 2 = true := by decide +kernel
theorem k162_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k162_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k162_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s162_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k162_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k162_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k162_3_3_26 k h.1 (by omega)
theorem s162_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 4 = true := by decide +kernel
theorem s162_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 5 = true := by decide +kernel
theorem k162_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k162_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k162_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k162_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k162_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k162_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k162_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k162_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k162_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k162_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k162_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s162_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k162_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k162_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k162_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k162_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k162_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k162_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k162_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k162_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k162_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k162_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k162_3_6_130 k h.1 (by omega)
theorem s162_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 3 7 = true := by decide +kernel
theorem s162_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 0 = true := by decide +kernel
theorem s162_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 1 = true := by decide +kernel
theorem s162_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 2 = true := by decide +kernel
theorem s162_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 3 = true := by decide +kernel
theorem s162_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 4 = true := by decide +kernel
theorem s162_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 5 = true := by decide +kernel
theorem k162_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k162_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k162_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k162_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k162_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k162_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k162_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s162_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k162_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k162_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k162_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k162_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k162_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k162_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k162_4_6_126 k h.1 (by omega)
theorem s162_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 4 7 = true := by decide +kernel
theorem s162_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 0 = true := by decide +kernel
theorem s162_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 1 = true := by decide +kernel
theorem s162_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 2 = true := by decide +kernel
theorem s162_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 3 = true := by decide +kernel
theorem s162_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 4 = true := by decide +kernel
theorem s162_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 5 = true := by decide +kernel
theorem k162_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k162_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k162_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k162_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k162_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k162_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k162_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s162_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k162_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k162_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k162_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k162_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k162_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k162_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 162) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (162 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k162_5_6_126 k h.1 (by omega)
theorem s162_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 5 7 = true := by decide +kernel
theorem s162_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 0 = true := by decide +kernel
theorem s162_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 1 = true := by decide +kernel
theorem s162_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 2 = true := by decide +kernel
theorem s162_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 3 = true := by decide +kernel
theorem s162_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 4 = true := by decide +kernel
theorem s162_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 5 = true := by decide +kernel
theorem s162_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 6 = true := by decide +kernel
theorem k162_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k162_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k162_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k162_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k162_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s162_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k162_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k162_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k162_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k162_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 162) ((InDA1.TCasaD 6 6 7).getD (162 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k162_6_7_12 k h.1 (by omega)
theorem col162_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 7 v) = true := by decide +kernel
theorem col162 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 162) 162 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col162_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col162_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col162_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s162_3_0
    · exact s162_3_1
    · exact s162_3_2
    · exact s162_3_3
    · exact s162_3_4
    · exact s162_3_5
    · exact s162_3_6
    · exact s162_3_7
  · fin_cases v
    · exact s162_4_0
    · exact s162_4_1
    · exact s162_4_2
    · exact s162_4_3
    · exact s162_4_4
    · exact s162_4_5
    · exact s162_4_6
    · exact s162_4_7
  · fin_cases v
    · exact s162_5_0
    · exact s162_5_1
    · exact s162_5_2
    · exact s162_5_3
    · exact s162_5_4
    · exact s162_5_5
    · exact s162_5_6
    · exact s162_5_7
  · fin_cases v
    · exact s162_6_0
    · exact s162_6_1
    · exact s162_6_2
    · exact s162_6_3
    · exact s162_6_4
    · exact s162_6_5
    · exact s162_6_6
    · exact s162_6_7
  · exact List.all_eq_true.mp col162_7 v (List.mem_finRange v)
theorem col163_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 0 v) = true := by decide +kernel
theorem col163_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 1 v) = true := by decide +kernel
theorem col163_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 2 v) = true := by decide +kernel
theorem s163_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 0 = true := by decide +kernel
theorem s163_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 1 = true := by decide +kernel
theorem s163_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 2 = true := by decide +kernel
theorem k163_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k163_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k163_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s163_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k163_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k163_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k163_3_3_26 k h.1 (by omega)
theorem s163_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 4 = true := by decide +kernel
theorem s163_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 5 = true := by decide +kernel
theorem k163_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k163_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k163_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k163_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k163_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k163_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k163_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k163_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k163_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k163_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k163_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s163_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k163_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k163_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k163_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k163_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k163_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k163_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k163_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k163_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k163_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k163_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k163_3_6_130 k h.1 (by omega)
theorem s163_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 3 7 = true := by decide +kernel
theorem s163_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 0 = true := by decide +kernel
theorem s163_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 1 = true := by decide +kernel
theorem s163_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 2 = true := by decide +kernel
theorem s163_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 3 = true := by decide +kernel
theorem s163_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 4 = true := by decide +kernel
theorem s163_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 5 = true := by decide +kernel
theorem k163_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k163_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k163_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k163_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k163_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k163_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k163_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s163_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k163_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k163_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k163_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k163_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k163_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k163_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k163_4_6_126 k h.1 (by omega)
theorem s163_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 4 7 = true := by decide +kernel
theorem s163_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 0 = true := by decide +kernel
theorem s163_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 1 = true := by decide +kernel
theorem s163_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 2 = true := by decide +kernel
theorem s163_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 3 = true := by decide +kernel
theorem s163_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 4 = true := by decide +kernel
theorem s163_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 5 = true := by decide +kernel
theorem k163_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k163_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k163_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k163_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k163_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k163_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k163_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s163_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k163_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k163_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k163_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k163_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k163_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k163_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 163) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (163 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k163_5_6_126 k h.1 (by omega)
theorem s163_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 5 7 = true := by decide +kernel
theorem s163_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 0 = true := by decide +kernel
theorem s163_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 1 = true := by decide +kernel
theorem s163_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 2 = true := by decide +kernel
theorem s163_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 3 = true := by decide +kernel
theorem s163_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 4 = true := by decide +kernel
theorem s163_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 5 = true := by decide +kernel
theorem s163_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 6 = true := by decide +kernel
theorem k163_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k163_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k163_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k163_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k163_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s163_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k163_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k163_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k163_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k163_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 163) ((InDA1.TCasaD 6 6 7).getD (163 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k163_6_7_12 k h.1 (by omega)
theorem col163_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 7 v) = true := by decide +kernel
theorem col163 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 163) 163 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col163_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col163_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col163_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s163_3_0
    · exact s163_3_1
    · exact s163_3_2
    · exact s163_3_3
    · exact s163_3_4
    · exact s163_3_5
    · exact s163_3_6
    · exact s163_3_7
  · fin_cases v
    · exact s163_4_0
    · exact s163_4_1
    · exact s163_4_2
    · exact s163_4_3
    · exact s163_4_4
    · exact s163_4_5
    · exact s163_4_6
    · exact s163_4_7
  · fin_cases v
    · exact s163_5_0
    · exact s163_5_1
    · exact s163_5_2
    · exact s163_5_3
    · exact s163_5_4
    · exact s163_5_5
    · exact s163_5_6
    · exact s163_5_7
  · fin_cases v
    · exact s163_6_0
    · exact s163_6_1
    · exact s163_6_2
    · exact s163_6_3
    · exact s163_6_4
    · exact s163_6_5
    · exact s163_6_6
    · exact s163_6_7
  · exact List.all_eq_true.mp col163_7 v (List.mem_finRange v)
theorem col164_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 0 v) = true := by decide +kernel
theorem col164_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 1 v) = true := by decide +kernel
theorem col164_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 2 v) = true := by decide +kernel
theorem s164_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 0 = true := by decide +kernel
theorem s164_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 1 = true := by decide +kernel
theorem s164_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 2 = true := by decide +kernel
theorem k164_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k164_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k164_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s164_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k164_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k164_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k164_3_3_26 k h.1 (by omega)
theorem s164_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 4 = true := by decide +kernel
theorem s164_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 5 = true := by decide +kernel
theorem k164_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k164_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k164_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k164_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k164_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k164_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k164_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k164_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k164_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k164_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k164_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s164_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k164_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k164_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k164_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k164_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k164_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k164_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k164_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k164_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k164_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k164_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k164_3_6_130 k h.1 (by omega)
theorem s164_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 3 7 = true := by decide +kernel
theorem s164_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 0 = true := by decide +kernel
theorem s164_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 1 = true := by decide +kernel
theorem s164_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 2 = true := by decide +kernel
theorem s164_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 3 = true := by decide +kernel
theorem s164_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 4 = true := by decide +kernel
theorem s164_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 5 = true := by decide +kernel
theorem k164_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k164_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k164_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k164_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k164_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k164_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k164_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s164_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k164_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k164_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k164_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k164_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k164_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k164_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k164_4_6_126 k h.1 (by omega)
theorem s164_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 4 7 = true := by decide +kernel
theorem s164_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 0 = true := by decide +kernel
theorem s164_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 1 = true := by decide +kernel
theorem s164_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 2 = true := by decide +kernel
theorem s164_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 3 = true := by decide +kernel
theorem s164_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 4 = true := by decide +kernel
theorem s164_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 5 = true := by decide +kernel
theorem k164_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k164_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k164_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k164_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k164_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k164_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k164_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s164_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k164_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k164_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k164_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k164_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k164_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k164_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 164) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (164 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k164_5_6_126 k h.1 (by omega)
theorem s164_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 5 7 = true := by decide +kernel
theorem s164_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 0 = true := by decide +kernel
theorem s164_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 1 = true := by decide +kernel
theorem s164_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 2 = true := by decide +kernel
theorem s164_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 3 = true := by decide +kernel
theorem s164_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 4 = true := by decide +kernel
theorem s164_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 5 = true := by decide +kernel
theorem s164_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 6 = true := by decide +kernel
theorem k164_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k164_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k164_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k164_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k164_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s164_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k164_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k164_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k164_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k164_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 164) ((InDA1.TCasaD 6 6 7).getD (164 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k164_6_7_12 k h.1 (by omega)
theorem col164_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 7 v) = true := by decide +kernel
theorem col164 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 164) 164 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col164_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col164_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col164_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s164_3_0
    · exact s164_3_1
    · exact s164_3_2
    · exact s164_3_3
    · exact s164_3_4
    · exact s164_3_5
    · exact s164_3_6
    · exact s164_3_7
  · fin_cases v
    · exact s164_4_0
    · exact s164_4_1
    · exact s164_4_2
    · exact s164_4_3
    · exact s164_4_4
    · exact s164_4_5
    · exact s164_4_6
    · exact s164_4_7
  · fin_cases v
    · exact s164_5_0
    · exact s164_5_1
    · exact s164_5_2
    · exact s164_5_3
    · exact s164_5_4
    · exact s164_5_5
    · exact s164_5_6
    · exact s164_5_7
  · fin_cases v
    · exact s164_6_0
    · exact s164_6_1
    · exact s164_6_2
    · exact s164_6_3
    · exact s164_6_4
    · exact s164_6_5
    · exact s164_6_6
    · exact s164_6_7
  · exact List.all_eq_true.mp col164_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
