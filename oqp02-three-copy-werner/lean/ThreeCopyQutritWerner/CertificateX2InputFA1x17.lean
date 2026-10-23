module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [85, 90). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col85_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 0 v) = true := by decide +kernel
theorem col85_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 1 v) = true := by decide +kernel
theorem col85_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 2 v) = true := by decide +kernel
theorem s85_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 0 = true := by decide +kernel
theorem s85_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 1 = true := by decide +kernel
theorem s85_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 2 = true := by decide +kernel
theorem k85_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k85_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k85_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s85_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k85_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k85_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k85_3_3_26 k h.1 (by omega)
theorem s85_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 4 = true := by decide +kernel
theorem s85_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 5 = true := by decide +kernel
theorem k85_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k85_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k85_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k85_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k85_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k85_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k85_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k85_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k85_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k85_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k85_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s85_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k85_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k85_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k85_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k85_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k85_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k85_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k85_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k85_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k85_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k85_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k85_3_6_130 k h.1 (by omega)
theorem s85_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 3 7 = true := by decide +kernel
theorem s85_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 0 = true := by decide +kernel
theorem s85_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 1 = true := by decide +kernel
theorem s85_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 2 = true := by decide +kernel
theorem s85_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 3 = true := by decide +kernel
theorem s85_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 4 = true := by decide +kernel
theorem s85_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 5 = true := by decide +kernel
theorem k85_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k85_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k85_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k85_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k85_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k85_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k85_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s85_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k85_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k85_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k85_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k85_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k85_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k85_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k85_4_6_126 k h.1 (by omega)
theorem s85_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 4 7 = true := by decide +kernel
theorem s85_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 0 = true := by decide +kernel
theorem s85_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 1 = true := by decide +kernel
theorem s85_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 2 = true := by decide +kernel
theorem s85_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 3 = true := by decide +kernel
theorem s85_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 4 = true := by decide +kernel
theorem s85_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 5 = true := by decide +kernel
theorem k85_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k85_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k85_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k85_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k85_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k85_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k85_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s85_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k85_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k85_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k85_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k85_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k85_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k85_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 85) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (85 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k85_5_6_126 k h.1 (by omega)
theorem s85_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 5 7 = true := by decide +kernel
theorem s85_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 0 = true := by decide +kernel
theorem s85_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 1 = true := by decide +kernel
theorem s85_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 2 = true := by decide +kernel
theorem s85_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 3 = true := by decide +kernel
theorem s85_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 4 = true := by decide +kernel
theorem s85_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 5 = true := by decide +kernel
theorem s85_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 6 = true := by decide +kernel
theorem k85_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k85_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k85_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k85_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k85_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s85_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k85_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k85_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k85_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k85_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 85) ((InDA1.TCasaD 6 6 7).getD (85 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k85_6_7_12 k h.1 (by omega)
theorem col85_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 7 v) = true := by decide +kernel
theorem col85 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 85) 85 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col85_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col85_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col85_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s85_3_0
    · exact s85_3_1
    · exact s85_3_2
    · exact s85_3_3
    · exact s85_3_4
    · exact s85_3_5
    · exact s85_3_6
    · exact s85_3_7
  · fin_cases v
    · exact s85_4_0
    · exact s85_4_1
    · exact s85_4_2
    · exact s85_4_3
    · exact s85_4_4
    · exact s85_4_5
    · exact s85_4_6
    · exact s85_4_7
  · fin_cases v
    · exact s85_5_0
    · exact s85_5_1
    · exact s85_5_2
    · exact s85_5_3
    · exact s85_5_4
    · exact s85_5_5
    · exact s85_5_6
    · exact s85_5_7
  · fin_cases v
    · exact s85_6_0
    · exact s85_6_1
    · exact s85_6_2
    · exact s85_6_3
    · exact s85_6_4
    · exact s85_6_5
    · exact s85_6_6
    · exact s85_6_7
  · exact List.all_eq_true.mp col85_7 v (List.mem_finRange v)
theorem col86_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 0 v) = true := by decide +kernel
theorem col86_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 1 v) = true := by decide +kernel
theorem col86_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 2 v) = true := by decide +kernel
theorem s86_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 0 = true := by decide +kernel
theorem s86_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 1 = true := by decide +kernel
theorem s86_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 2 = true := by decide +kernel
theorem k86_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k86_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k86_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s86_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k86_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k86_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k86_3_3_26 k h.1 (by omega)
theorem s86_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 4 = true := by decide +kernel
theorem s86_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 5 = true := by decide +kernel
theorem k86_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k86_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k86_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k86_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k86_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k86_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k86_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k86_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k86_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k86_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k86_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s86_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k86_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k86_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k86_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k86_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k86_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k86_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k86_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k86_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k86_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k86_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k86_3_6_130 k h.1 (by omega)
theorem s86_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 3 7 = true := by decide +kernel
theorem s86_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 0 = true := by decide +kernel
theorem s86_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 1 = true := by decide +kernel
theorem s86_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 2 = true := by decide +kernel
theorem s86_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 3 = true := by decide +kernel
theorem s86_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 4 = true := by decide +kernel
theorem s86_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 5 = true := by decide +kernel
theorem k86_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k86_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k86_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k86_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k86_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k86_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k86_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s86_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k86_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k86_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k86_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k86_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k86_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k86_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k86_4_6_126 k h.1 (by omega)
theorem s86_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 4 7 = true := by decide +kernel
theorem s86_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 0 = true := by decide +kernel
theorem s86_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 1 = true := by decide +kernel
theorem s86_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 2 = true := by decide +kernel
theorem s86_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 3 = true := by decide +kernel
theorem s86_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 4 = true := by decide +kernel
theorem s86_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 5 = true := by decide +kernel
theorem k86_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k86_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k86_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k86_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k86_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k86_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k86_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s86_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k86_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k86_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k86_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k86_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k86_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k86_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 86) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (86 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k86_5_6_126 k h.1 (by omega)
theorem s86_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 5 7 = true := by decide +kernel
theorem s86_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 0 = true := by decide +kernel
theorem s86_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 1 = true := by decide +kernel
theorem s86_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 2 = true := by decide +kernel
theorem s86_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 3 = true := by decide +kernel
theorem s86_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 4 = true := by decide +kernel
theorem s86_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 5 = true := by decide +kernel
theorem s86_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 6 = true := by decide +kernel
theorem k86_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k86_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k86_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k86_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k86_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s86_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k86_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k86_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k86_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k86_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 86) ((InDA1.TCasaD 6 6 7).getD (86 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k86_6_7_12 k h.1 (by omega)
theorem col86_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 7 v) = true := by decide +kernel
theorem col86 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 86) 86 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col86_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col86_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col86_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s86_3_0
    · exact s86_3_1
    · exact s86_3_2
    · exact s86_3_3
    · exact s86_3_4
    · exact s86_3_5
    · exact s86_3_6
    · exact s86_3_7
  · fin_cases v
    · exact s86_4_0
    · exact s86_4_1
    · exact s86_4_2
    · exact s86_4_3
    · exact s86_4_4
    · exact s86_4_5
    · exact s86_4_6
    · exact s86_4_7
  · fin_cases v
    · exact s86_5_0
    · exact s86_5_1
    · exact s86_5_2
    · exact s86_5_3
    · exact s86_5_4
    · exact s86_5_5
    · exact s86_5_6
    · exact s86_5_7
  · fin_cases v
    · exact s86_6_0
    · exact s86_6_1
    · exact s86_6_2
    · exact s86_6_3
    · exact s86_6_4
    · exact s86_6_5
    · exact s86_6_6
    · exact s86_6_7
  · exact List.all_eq_true.mp col86_7 v (List.mem_finRange v)
theorem col87_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 0 v) = true := by decide +kernel
theorem col87_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 1 v) = true := by decide +kernel
theorem col87_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 2 v) = true := by decide +kernel
theorem s87_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 0 = true := by decide +kernel
theorem s87_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 1 = true := by decide +kernel
theorem s87_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 2 = true := by decide +kernel
theorem k87_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k87_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k87_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s87_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k87_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k87_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k87_3_3_26 k h.1 (by omega)
theorem s87_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 4 = true := by decide +kernel
theorem s87_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 5 = true := by decide +kernel
theorem k87_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k87_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k87_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k87_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k87_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k87_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k87_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k87_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k87_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k87_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k87_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s87_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k87_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k87_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k87_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k87_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k87_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k87_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k87_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k87_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k87_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k87_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k87_3_6_130 k h.1 (by omega)
theorem s87_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 3 7 = true := by decide +kernel
theorem s87_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 0 = true := by decide +kernel
theorem s87_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 1 = true := by decide +kernel
theorem s87_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 2 = true := by decide +kernel
theorem s87_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 3 = true := by decide +kernel
theorem s87_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 4 = true := by decide +kernel
theorem s87_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 5 = true := by decide +kernel
theorem k87_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k87_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k87_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k87_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k87_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k87_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k87_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s87_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k87_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k87_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k87_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k87_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k87_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k87_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k87_4_6_126 k h.1 (by omega)
theorem s87_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 4 7 = true := by decide +kernel
theorem s87_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 0 = true := by decide +kernel
theorem s87_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 1 = true := by decide +kernel
theorem s87_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 2 = true := by decide +kernel
theorem s87_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 3 = true := by decide +kernel
theorem s87_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 4 = true := by decide +kernel
theorem s87_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 5 = true := by decide +kernel
theorem k87_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k87_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k87_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k87_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k87_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k87_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k87_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s87_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k87_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k87_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k87_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k87_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k87_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k87_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 87) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (87 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k87_5_6_126 k h.1 (by omega)
theorem s87_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 5 7 = true := by decide +kernel
theorem s87_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 0 = true := by decide +kernel
theorem s87_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 1 = true := by decide +kernel
theorem s87_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 2 = true := by decide +kernel
theorem s87_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 3 = true := by decide +kernel
theorem s87_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 4 = true := by decide +kernel
theorem s87_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 5 = true := by decide +kernel
theorem s87_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 6 = true := by decide +kernel
theorem k87_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k87_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k87_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k87_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k87_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s87_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k87_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k87_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k87_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k87_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 87) ((InDA1.TCasaD 6 6 7).getD (87 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k87_6_7_12 k h.1 (by omega)
theorem col87_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 7 v) = true := by decide +kernel
theorem col87 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 87) 87 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col87_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col87_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col87_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s87_3_0
    · exact s87_3_1
    · exact s87_3_2
    · exact s87_3_3
    · exact s87_3_4
    · exact s87_3_5
    · exact s87_3_6
    · exact s87_3_7
  · fin_cases v
    · exact s87_4_0
    · exact s87_4_1
    · exact s87_4_2
    · exact s87_4_3
    · exact s87_4_4
    · exact s87_4_5
    · exact s87_4_6
    · exact s87_4_7
  · fin_cases v
    · exact s87_5_0
    · exact s87_5_1
    · exact s87_5_2
    · exact s87_5_3
    · exact s87_5_4
    · exact s87_5_5
    · exact s87_5_6
    · exact s87_5_7
  · fin_cases v
    · exact s87_6_0
    · exact s87_6_1
    · exact s87_6_2
    · exact s87_6_3
    · exact s87_6_4
    · exact s87_6_5
    · exact s87_6_6
    · exact s87_6_7
  · exact List.all_eq_true.mp col87_7 v (List.mem_finRange v)
theorem col88_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 0 v) = true := by decide +kernel
theorem col88_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 1 v) = true := by decide +kernel
theorem col88_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 2 v) = true := by decide +kernel
theorem s88_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 0 = true := by decide +kernel
theorem s88_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 1 = true := by decide +kernel
theorem s88_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 2 = true := by decide +kernel
theorem k88_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k88_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k88_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s88_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k88_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k88_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k88_3_3_26 k h.1 (by omega)
theorem s88_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 4 = true := by decide +kernel
theorem s88_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 5 = true := by decide +kernel
theorem k88_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k88_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k88_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k88_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k88_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k88_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k88_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k88_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k88_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k88_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k88_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s88_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k88_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k88_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k88_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k88_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k88_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k88_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k88_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k88_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k88_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k88_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k88_3_6_130 k h.1 (by omega)
theorem s88_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 3 7 = true := by decide +kernel
theorem s88_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 0 = true := by decide +kernel
theorem s88_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 1 = true := by decide +kernel
theorem s88_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 2 = true := by decide +kernel
theorem s88_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 3 = true := by decide +kernel
theorem s88_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 4 = true := by decide +kernel
theorem s88_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 5 = true := by decide +kernel
theorem k88_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k88_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k88_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k88_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k88_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k88_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k88_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s88_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k88_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k88_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k88_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k88_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k88_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k88_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k88_4_6_126 k h.1 (by omega)
theorem s88_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 4 7 = true := by decide +kernel
theorem s88_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 0 = true := by decide +kernel
theorem s88_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 1 = true := by decide +kernel
theorem s88_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 2 = true := by decide +kernel
theorem s88_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 3 = true := by decide +kernel
theorem s88_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 4 = true := by decide +kernel
theorem s88_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 5 = true := by decide +kernel
theorem k88_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k88_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k88_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k88_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k88_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k88_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k88_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s88_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k88_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k88_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k88_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k88_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k88_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k88_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 88) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (88 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k88_5_6_126 k h.1 (by omega)
theorem s88_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 5 7 = true := by decide +kernel
theorem s88_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 0 = true := by decide +kernel
theorem s88_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 1 = true := by decide +kernel
theorem s88_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 2 = true := by decide +kernel
theorem s88_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 3 = true := by decide +kernel
theorem s88_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 4 = true := by decide +kernel
theorem s88_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 5 = true := by decide +kernel
theorem s88_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 6 = true := by decide +kernel
theorem k88_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k88_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k88_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k88_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k88_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s88_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k88_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k88_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k88_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k88_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 88) ((InDA1.TCasaD 6 6 7).getD (88 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k88_6_7_12 k h.1 (by omega)
theorem col88_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 7 v) = true := by decide +kernel
theorem col88 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 88) 88 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col88_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col88_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col88_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s88_3_0
    · exact s88_3_1
    · exact s88_3_2
    · exact s88_3_3
    · exact s88_3_4
    · exact s88_3_5
    · exact s88_3_6
    · exact s88_3_7
  · fin_cases v
    · exact s88_4_0
    · exact s88_4_1
    · exact s88_4_2
    · exact s88_4_3
    · exact s88_4_4
    · exact s88_4_5
    · exact s88_4_6
    · exact s88_4_7
  · fin_cases v
    · exact s88_5_0
    · exact s88_5_1
    · exact s88_5_2
    · exact s88_5_3
    · exact s88_5_4
    · exact s88_5_5
    · exact s88_5_6
    · exact s88_5_7
  · fin_cases v
    · exact s88_6_0
    · exact s88_6_1
    · exact s88_6_2
    · exact s88_6_3
    · exact s88_6_4
    · exact s88_6_5
    · exact s88_6_6
    · exact s88_6_7
  · exact List.all_eq_true.mp col88_7 v (List.mem_finRange v)
theorem col89_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 0 v) = true := by decide +kernel
theorem col89_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 1 v) = true := by decide +kernel
theorem col89_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 2 v) = true := by decide +kernel
theorem s89_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 0 = true := by decide +kernel
theorem s89_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 1 = true := by decide +kernel
theorem s89_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 2 = true := by decide +kernel
theorem k89_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k89_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k89_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s89_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k89_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k89_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k89_3_3_26 k h.1 (by omega)
theorem s89_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 4 = true := by decide +kernel
theorem s89_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 5 = true := by decide +kernel
theorem k89_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k89_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k89_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k89_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k89_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k89_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k89_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k89_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k89_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k89_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k89_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s89_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k89_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k89_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k89_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k89_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k89_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k89_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k89_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k89_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k89_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k89_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k89_3_6_130 k h.1 (by omega)
theorem s89_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 3 7 = true := by decide +kernel
theorem s89_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 0 = true := by decide +kernel
theorem s89_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 1 = true := by decide +kernel
theorem s89_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 2 = true := by decide +kernel
theorem s89_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 3 = true := by decide +kernel
theorem s89_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 4 = true := by decide +kernel
theorem s89_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 5 = true := by decide +kernel
theorem k89_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k89_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k89_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k89_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k89_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k89_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k89_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s89_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k89_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k89_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k89_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k89_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k89_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k89_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k89_4_6_126 k h.1 (by omega)
theorem s89_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 4 7 = true := by decide +kernel
theorem s89_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 0 = true := by decide +kernel
theorem s89_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 1 = true := by decide +kernel
theorem s89_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 2 = true := by decide +kernel
theorem s89_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 3 = true := by decide +kernel
theorem s89_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 4 = true := by decide +kernel
theorem s89_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 5 = true := by decide +kernel
theorem k89_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k89_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k89_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k89_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k89_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k89_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k89_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s89_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k89_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k89_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k89_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k89_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k89_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k89_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 89) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (89 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k89_5_6_126 k h.1 (by omega)
theorem s89_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 5 7 = true := by decide +kernel
theorem s89_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 0 = true := by decide +kernel
theorem s89_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 1 = true := by decide +kernel
theorem s89_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 2 = true := by decide +kernel
theorem s89_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 3 = true := by decide +kernel
theorem s89_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 4 = true := by decide +kernel
theorem s89_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 5 = true := by decide +kernel
theorem s89_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 6 = true := by decide +kernel
theorem k89_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k89_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k89_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k89_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k89_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s89_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k89_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k89_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k89_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k89_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 89) ((InDA1.TCasaD 6 6 7).getD (89 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k89_6_7_12 k h.1 (by omega)
theorem col89_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 7 v) = true := by decide +kernel
theorem col89 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 89) 89 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col89_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col89_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col89_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s89_3_0
    · exact s89_3_1
    · exact s89_3_2
    · exact s89_3_3
    · exact s89_3_4
    · exact s89_3_5
    · exact s89_3_6
    · exact s89_3_7
  · fin_cases v
    · exact s89_4_0
    · exact s89_4_1
    · exact s89_4_2
    · exact s89_4_3
    · exact s89_4_4
    · exact s89_4_5
    · exact s89_4_6
    · exact s89_4_7
  · fin_cases v
    · exact s89_5_0
    · exact s89_5_1
    · exact s89_5_2
    · exact s89_5_3
    · exact s89_5_4
    · exact s89_5_5
    · exact s89_5_6
    · exact s89_5_7
  · fin_cases v
    · exact s89_6_0
    · exact s89_6_1
    · exact s89_6_2
    · exact s89_6_3
    · exact s89_6_4
    · exact s89_6_5
    · exact s89_6_6
    · exact s89_6_7
  · exact List.all_eq_true.mp col89_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
