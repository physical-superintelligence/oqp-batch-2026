module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [150, 155). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col150_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 0 v) = true := by decide +kernel
theorem col150_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 1 v) = true := by decide +kernel
theorem col150_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 2 v) = true := by decide +kernel
theorem s150_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 0 = true := by decide +kernel
theorem s150_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 1 = true := by decide +kernel
theorem s150_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 2 = true := by decide +kernel
theorem k150_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k150_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k150_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s150_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k150_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k150_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k150_3_3_26 k h.1 (by omega)
theorem s150_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 4 = true := by decide +kernel
theorem s150_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 5 = true := by decide +kernel
theorem k150_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k150_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k150_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k150_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k150_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k150_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k150_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k150_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k150_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k150_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k150_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s150_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k150_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k150_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k150_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k150_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k150_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k150_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k150_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k150_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k150_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k150_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k150_3_6_130 k h.1 (by omega)
theorem s150_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 3 7 = true := by decide +kernel
theorem s150_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 0 = true := by decide +kernel
theorem s150_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 1 = true := by decide +kernel
theorem s150_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 2 = true := by decide +kernel
theorem s150_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 3 = true := by decide +kernel
theorem s150_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 4 = true := by decide +kernel
theorem s150_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 5 = true := by decide +kernel
theorem k150_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k150_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k150_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k150_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k150_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k150_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k150_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s150_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k150_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k150_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k150_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k150_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k150_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k150_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k150_4_6_126 k h.1 (by omega)
theorem s150_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 4 7 = true := by decide +kernel
theorem s150_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 0 = true := by decide +kernel
theorem s150_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 1 = true := by decide +kernel
theorem s150_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 2 = true := by decide +kernel
theorem s150_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 3 = true := by decide +kernel
theorem s150_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 4 = true := by decide +kernel
theorem s150_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 5 = true := by decide +kernel
theorem k150_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k150_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k150_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k150_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k150_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k150_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k150_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s150_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k150_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k150_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k150_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k150_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k150_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k150_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 150) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (150 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k150_5_6_126 k h.1 (by omega)
theorem s150_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 5 7 = true := by decide +kernel
theorem s150_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 0 = true := by decide +kernel
theorem s150_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 1 = true := by decide +kernel
theorem s150_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 2 = true := by decide +kernel
theorem s150_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 3 = true := by decide +kernel
theorem s150_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 4 = true := by decide +kernel
theorem s150_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 5 = true := by decide +kernel
theorem s150_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 6 = true := by decide +kernel
theorem k150_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k150_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k150_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k150_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k150_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s150_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k150_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k150_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k150_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k150_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 150) ((InDA1.TCasaD 6 6 7).getD (150 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k150_6_7_12 k h.1 (by omega)
theorem col150_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 7 v) = true := by decide +kernel
theorem col150 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 150) 150 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col150_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col150_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col150_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s150_3_0
    · exact s150_3_1
    · exact s150_3_2
    · exact s150_3_3
    · exact s150_3_4
    · exact s150_3_5
    · exact s150_3_6
    · exact s150_3_7
  · fin_cases v
    · exact s150_4_0
    · exact s150_4_1
    · exact s150_4_2
    · exact s150_4_3
    · exact s150_4_4
    · exact s150_4_5
    · exact s150_4_6
    · exact s150_4_7
  · fin_cases v
    · exact s150_5_0
    · exact s150_5_1
    · exact s150_5_2
    · exact s150_5_3
    · exact s150_5_4
    · exact s150_5_5
    · exact s150_5_6
    · exact s150_5_7
  · fin_cases v
    · exact s150_6_0
    · exact s150_6_1
    · exact s150_6_2
    · exact s150_6_3
    · exact s150_6_4
    · exact s150_6_5
    · exact s150_6_6
    · exact s150_6_7
  · exact List.all_eq_true.mp col150_7 v (List.mem_finRange v)
theorem col151_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 0 v) = true := by decide +kernel
theorem col151_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 1 v) = true := by decide +kernel
theorem col151_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 2 v) = true := by decide +kernel
theorem s151_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 0 = true := by decide +kernel
theorem s151_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 1 = true := by decide +kernel
theorem s151_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 2 = true := by decide +kernel
theorem k151_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k151_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k151_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s151_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k151_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k151_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k151_3_3_26 k h.1 (by omega)
theorem s151_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 4 = true := by decide +kernel
theorem s151_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 5 = true := by decide +kernel
theorem k151_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k151_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k151_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k151_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k151_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k151_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k151_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k151_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k151_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k151_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k151_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s151_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k151_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k151_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k151_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k151_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k151_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k151_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k151_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k151_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k151_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k151_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k151_3_6_130 k h.1 (by omega)
theorem s151_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 3 7 = true := by decide +kernel
theorem s151_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 0 = true := by decide +kernel
theorem s151_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 1 = true := by decide +kernel
theorem s151_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 2 = true := by decide +kernel
theorem s151_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 3 = true := by decide +kernel
theorem s151_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 4 = true := by decide +kernel
theorem s151_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 5 = true := by decide +kernel
theorem k151_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k151_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k151_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k151_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k151_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k151_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k151_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s151_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k151_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k151_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k151_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k151_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k151_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k151_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k151_4_6_126 k h.1 (by omega)
theorem s151_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 4 7 = true := by decide +kernel
theorem s151_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 0 = true := by decide +kernel
theorem s151_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 1 = true := by decide +kernel
theorem s151_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 2 = true := by decide +kernel
theorem s151_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 3 = true := by decide +kernel
theorem s151_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 4 = true := by decide +kernel
theorem s151_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 5 = true := by decide +kernel
theorem k151_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k151_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k151_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k151_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k151_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k151_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k151_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s151_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k151_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k151_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k151_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k151_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k151_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k151_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 151) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (151 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k151_5_6_126 k h.1 (by omega)
theorem s151_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 5 7 = true := by decide +kernel
theorem s151_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 0 = true := by decide +kernel
theorem s151_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 1 = true := by decide +kernel
theorem s151_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 2 = true := by decide +kernel
theorem s151_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 3 = true := by decide +kernel
theorem s151_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 4 = true := by decide +kernel
theorem s151_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 5 = true := by decide +kernel
theorem s151_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 6 = true := by decide +kernel
theorem k151_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k151_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k151_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k151_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k151_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s151_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k151_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k151_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k151_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k151_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 151) ((InDA1.TCasaD 6 6 7).getD (151 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k151_6_7_12 k h.1 (by omega)
theorem col151_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 7 v) = true := by decide +kernel
theorem col151 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 151) 151 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col151_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col151_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col151_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s151_3_0
    · exact s151_3_1
    · exact s151_3_2
    · exact s151_3_3
    · exact s151_3_4
    · exact s151_3_5
    · exact s151_3_6
    · exact s151_3_7
  · fin_cases v
    · exact s151_4_0
    · exact s151_4_1
    · exact s151_4_2
    · exact s151_4_3
    · exact s151_4_4
    · exact s151_4_5
    · exact s151_4_6
    · exact s151_4_7
  · fin_cases v
    · exact s151_5_0
    · exact s151_5_1
    · exact s151_5_2
    · exact s151_5_3
    · exact s151_5_4
    · exact s151_5_5
    · exact s151_5_6
    · exact s151_5_7
  · fin_cases v
    · exact s151_6_0
    · exact s151_6_1
    · exact s151_6_2
    · exact s151_6_3
    · exact s151_6_4
    · exact s151_6_5
    · exact s151_6_6
    · exact s151_6_7
  · exact List.all_eq_true.mp col151_7 v (List.mem_finRange v)
theorem col152_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 0 v) = true := by decide +kernel
theorem col152_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 1 v) = true := by decide +kernel
theorem col152_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 2 v) = true := by decide +kernel
theorem s152_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 0 = true := by decide +kernel
theorem s152_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 1 = true := by decide +kernel
theorem s152_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 2 = true := by decide +kernel
theorem k152_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k152_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k152_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s152_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k152_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k152_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k152_3_3_26 k h.1 (by omega)
theorem s152_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 4 = true := by decide +kernel
theorem s152_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 5 = true := by decide +kernel
theorem k152_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k152_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k152_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k152_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k152_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k152_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k152_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k152_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k152_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k152_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k152_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s152_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k152_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k152_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k152_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k152_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k152_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k152_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k152_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k152_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k152_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k152_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k152_3_6_130 k h.1 (by omega)
theorem s152_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 3 7 = true := by decide +kernel
theorem s152_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 0 = true := by decide +kernel
theorem s152_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 1 = true := by decide +kernel
theorem s152_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 2 = true := by decide +kernel
theorem s152_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 3 = true := by decide +kernel
theorem s152_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 4 = true := by decide +kernel
theorem s152_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 5 = true := by decide +kernel
theorem k152_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k152_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k152_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k152_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k152_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k152_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k152_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s152_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k152_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k152_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k152_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k152_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k152_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k152_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k152_4_6_126 k h.1 (by omega)
theorem s152_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 4 7 = true := by decide +kernel
theorem s152_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 0 = true := by decide +kernel
theorem s152_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 1 = true := by decide +kernel
theorem s152_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 2 = true := by decide +kernel
theorem s152_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 3 = true := by decide +kernel
theorem s152_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 4 = true := by decide +kernel
theorem s152_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 5 = true := by decide +kernel
theorem k152_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k152_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k152_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k152_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k152_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k152_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k152_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s152_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k152_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k152_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k152_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k152_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k152_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k152_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 152) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (152 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k152_5_6_126 k h.1 (by omega)
theorem s152_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 5 7 = true := by decide +kernel
theorem s152_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 0 = true := by decide +kernel
theorem s152_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 1 = true := by decide +kernel
theorem s152_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 2 = true := by decide +kernel
theorem s152_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 3 = true := by decide +kernel
theorem s152_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 4 = true := by decide +kernel
theorem s152_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 5 = true := by decide +kernel
theorem s152_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 6 = true := by decide +kernel
theorem k152_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k152_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k152_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k152_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k152_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s152_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k152_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k152_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k152_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k152_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 152) ((InDA1.TCasaD 6 6 7).getD (152 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k152_6_7_12 k h.1 (by omega)
theorem col152_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 7 v) = true := by decide +kernel
theorem col152 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 152) 152 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col152_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col152_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col152_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s152_3_0
    · exact s152_3_1
    · exact s152_3_2
    · exact s152_3_3
    · exact s152_3_4
    · exact s152_3_5
    · exact s152_3_6
    · exact s152_3_7
  · fin_cases v
    · exact s152_4_0
    · exact s152_4_1
    · exact s152_4_2
    · exact s152_4_3
    · exact s152_4_4
    · exact s152_4_5
    · exact s152_4_6
    · exact s152_4_7
  · fin_cases v
    · exact s152_5_0
    · exact s152_5_1
    · exact s152_5_2
    · exact s152_5_3
    · exact s152_5_4
    · exact s152_5_5
    · exact s152_5_6
    · exact s152_5_7
  · fin_cases v
    · exact s152_6_0
    · exact s152_6_1
    · exact s152_6_2
    · exact s152_6_3
    · exact s152_6_4
    · exact s152_6_5
    · exact s152_6_6
    · exact s152_6_7
  · exact List.all_eq_true.mp col152_7 v (List.mem_finRange v)
theorem col153_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 0 v) = true := by decide +kernel
theorem col153_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 1 v) = true := by decide +kernel
theorem col153_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 2 v) = true := by decide +kernel
theorem s153_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 0 = true := by decide +kernel
theorem s153_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 1 = true := by decide +kernel
theorem s153_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 2 = true := by decide +kernel
theorem k153_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k153_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k153_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s153_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k153_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k153_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k153_3_3_26 k h.1 (by omega)
theorem s153_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 4 = true := by decide +kernel
theorem s153_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 5 = true := by decide +kernel
theorem k153_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k153_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k153_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k153_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k153_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k153_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k153_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k153_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k153_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k153_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k153_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s153_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k153_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k153_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k153_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k153_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k153_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k153_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k153_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k153_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k153_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k153_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k153_3_6_130 k h.1 (by omega)
theorem s153_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 3 7 = true := by decide +kernel
theorem s153_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 0 = true := by decide +kernel
theorem s153_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 1 = true := by decide +kernel
theorem s153_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 2 = true := by decide +kernel
theorem s153_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 3 = true := by decide +kernel
theorem s153_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 4 = true := by decide +kernel
theorem s153_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 5 = true := by decide +kernel
theorem k153_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k153_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k153_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k153_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k153_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k153_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k153_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s153_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k153_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k153_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k153_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k153_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k153_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k153_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k153_4_6_126 k h.1 (by omega)
theorem s153_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 4 7 = true := by decide +kernel
theorem s153_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 0 = true := by decide +kernel
theorem s153_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 1 = true := by decide +kernel
theorem s153_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 2 = true := by decide +kernel
theorem s153_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 3 = true := by decide +kernel
theorem s153_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 4 = true := by decide +kernel
theorem s153_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 5 = true := by decide +kernel
theorem k153_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k153_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k153_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k153_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k153_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k153_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k153_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s153_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k153_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k153_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k153_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k153_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k153_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k153_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 153) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (153 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k153_5_6_126 k h.1 (by omega)
theorem s153_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 5 7 = true := by decide +kernel
theorem s153_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 0 = true := by decide +kernel
theorem s153_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 1 = true := by decide +kernel
theorem s153_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 2 = true := by decide +kernel
theorem s153_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 3 = true := by decide +kernel
theorem s153_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 4 = true := by decide +kernel
theorem s153_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 5 = true := by decide +kernel
theorem s153_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 6 = true := by decide +kernel
theorem k153_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k153_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k153_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k153_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k153_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s153_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k153_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k153_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k153_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k153_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 153) ((InDA1.TCasaD 6 6 7).getD (153 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k153_6_7_12 k h.1 (by omega)
theorem col153_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 7 v) = true := by decide +kernel
theorem col153 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 153) 153 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col153_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col153_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col153_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s153_3_0
    · exact s153_3_1
    · exact s153_3_2
    · exact s153_3_3
    · exact s153_3_4
    · exact s153_3_5
    · exact s153_3_6
    · exact s153_3_7
  · fin_cases v
    · exact s153_4_0
    · exact s153_4_1
    · exact s153_4_2
    · exact s153_4_3
    · exact s153_4_4
    · exact s153_4_5
    · exact s153_4_6
    · exact s153_4_7
  · fin_cases v
    · exact s153_5_0
    · exact s153_5_1
    · exact s153_5_2
    · exact s153_5_3
    · exact s153_5_4
    · exact s153_5_5
    · exact s153_5_6
    · exact s153_5_7
  · fin_cases v
    · exact s153_6_0
    · exact s153_6_1
    · exact s153_6_2
    · exact s153_6_3
    · exact s153_6_4
    · exact s153_6_5
    · exact s153_6_6
    · exact s153_6_7
  · exact List.all_eq_true.mp col153_7 v (List.mem_finRange v)
theorem col154_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 0 v) = true := by decide +kernel
theorem col154_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 1 v) = true := by decide +kernel
theorem col154_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 2 v) = true := by decide +kernel
theorem s154_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 0 = true := by decide +kernel
theorem s154_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 1 = true := by decide +kernel
theorem s154_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 2 = true := by decide +kernel
theorem k154_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k154_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k154_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s154_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k154_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k154_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k154_3_3_26 k h.1 (by omega)
theorem s154_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 4 = true := by decide +kernel
theorem s154_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 5 = true := by decide +kernel
theorem k154_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k154_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k154_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k154_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k154_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k154_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k154_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k154_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k154_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k154_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k154_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s154_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k154_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k154_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k154_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k154_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k154_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k154_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k154_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k154_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k154_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k154_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k154_3_6_130 k h.1 (by omega)
theorem s154_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 3 7 = true := by decide +kernel
theorem s154_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 0 = true := by decide +kernel
theorem s154_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 1 = true := by decide +kernel
theorem s154_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 2 = true := by decide +kernel
theorem s154_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 3 = true := by decide +kernel
theorem s154_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 4 = true := by decide +kernel
theorem s154_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 5 = true := by decide +kernel
theorem k154_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k154_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k154_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k154_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k154_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k154_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k154_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s154_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k154_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k154_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k154_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k154_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k154_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k154_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k154_4_6_126 k h.1 (by omega)
theorem s154_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 4 7 = true := by decide +kernel
theorem s154_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 0 = true := by decide +kernel
theorem s154_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 1 = true := by decide +kernel
theorem s154_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 2 = true := by decide +kernel
theorem s154_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 3 = true := by decide +kernel
theorem s154_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 4 = true := by decide +kernel
theorem s154_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 5 = true := by decide +kernel
theorem k154_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k154_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k154_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k154_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k154_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k154_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k154_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s154_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k154_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k154_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k154_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k154_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k154_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k154_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 154) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (154 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k154_5_6_126 k h.1 (by omega)
theorem s154_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 5 7 = true := by decide +kernel
theorem s154_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 0 = true := by decide +kernel
theorem s154_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 1 = true := by decide +kernel
theorem s154_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 2 = true := by decide +kernel
theorem s154_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 3 = true := by decide +kernel
theorem s154_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 4 = true := by decide +kernel
theorem s154_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 5 = true := by decide +kernel
theorem s154_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 6 = true := by decide +kernel
theorem k154_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k154_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k154_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k154_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k154_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s154_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k154_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k154_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k154_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k154_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 154) ((InDA1.TCasaD 6 6 7).getD (154 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k154_6_7_12 k h.1 (by omega)
theorem col154_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 7 v) = true := by decide +kernel
theorem col154 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 154) 154 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col154_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col154_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col154_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s154_3_0
    · exact s154_3_1
    · exact s154_3_2
    · exact s154_3_3
    · exact s154_3_4
    · exact s154_3_5
    · exact s154_3_6
    · exact s154_3_7
  · fin_cases v
    · exact s154_4_0
    · exact s154_4_1
    · exact s154_4_2
    · exact s154_4_3
    · exact s154_4_4
    · exact s154_4_5
    · exact s154_4_6
    · exact s154_4_7
  · fin_cases v
    · exact s154_5_0
    · exact s154_5_1
    · exact s154_5_2
    · exact s154_5_3
    · exact s154_5_4
    · exact s154_5_5
    · exact s154_5_6
    · exact s154_5_7
  · fin_cases v
    · exact s154_6_0
    · exact s154_6_1
    · exact s154_6_2
    · exact s154_6_3
    · exact s154_6_4
    · exact s154_6_5
    · exact s154_6_6
    · exact s154_6_7
  · exact List.all_eq_true.mp col154_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
