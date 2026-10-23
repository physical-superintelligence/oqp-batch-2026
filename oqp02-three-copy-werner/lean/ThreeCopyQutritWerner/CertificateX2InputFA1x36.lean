module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [180, 185). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col180_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 0 v) = true := by decide +kernel
theorem col180_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 1 v) = true := by decide +kernel
theorem col180_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 2 v) = true := by decide +kernel
theorem s180_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 0 = true := by decide +kernel
theorem s180_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 1 = true := by decide +kernel
theorem s180_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 2 = true := by decide +kernel
theorem k180_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k180_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k180_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s180_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k180_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k180_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k180_3_3_26 k h.1 (by omega)
theorem s180_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 4 = true := by decide +kernel
theorem s180_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 5 = true := by decide +kernel
theorem k180_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k180_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k180_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k180_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k180_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k180_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k180_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k180_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k180_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k180_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k180_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s180_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k180_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k180_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k180_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k180_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k180_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k180_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k180_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k180_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k180_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k180_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k180_3_6_130 k h.1 (by omega)
theorem s180_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 3 7 = true := by decide +kernel
theorem s180_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 0 = true := by decide +kernel
theorem s180_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 1 = true := by decide +kernel
theorem s180_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 2 = true := by decide +kernel
theorem s180_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 3 = true := by decide +kernel
theorem s180_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 4 = true := by decide +kernel
theorem s180_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 5 = true := by decide +kernel
theorem k180_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k180_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k180_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k180_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k180_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k180_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k180_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s180_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k180_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k180_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k180_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k180_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k180_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k180_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k180_4_6_126 k h.1 (by omega)
theorem s180_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 4 7 = true := by decide +kernel
theorem s180_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 0 = true := by decide +kernel
theorem s180_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 1 = true := by decide +kernel
theorem s180_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 2 = true := by decide +kernel
theorem s180_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 3 = true := by decide +kernel
theorem s180_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 4 = true := by decide +kernel
theorem s180_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 5 = true := by decide +kernel
theorem k180_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k180_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k180_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k180_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k180_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k180_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k180_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s180_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k180_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k180_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k180_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k180_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k180_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k180_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 180) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (180 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k180_5_6_126 k h.1 (by omega)
theorem s180_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 5 7 = true := by decide +kernel
theorem s180_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 0 = true := by decide +kernel
theorem s180_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 1 = true := by decide +kernel
theorem s180_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 2 = true := by decide +kernel
theorem s180_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 3 = true := by decide +kernel
theorem s180_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 4 = true := by decide +kernel
theorem s180_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 5 = true := by decide +kernel
theorem s180_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 6 = true := by decide +kernel
theorem k180_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k180_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k180_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k180_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k180_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s180_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k180_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k180_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k180_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k180_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 180) ((InDA1.TCasaD 6 6 7).getD (180 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k180_6_7_12 k h.1 (by omega)
theorem col180_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 7 v) = true := by decide +kernel
theorem col180 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 180) 180 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col180_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col180_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col180_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s180_3_0
    · exact s180_3_1
    · exact s180_3_2
    · exact s180_3_3
    · exact s180_3_4
    · exact s180_3_5
    · exact s180_3_6
    · exact s180_3_7
  · fin_cases v
    · exact s180_4_0
    · exact s180_4_1
    · exact s180_4_2
    · exact s180_4_3
    · exact s180_4_4
    · exact s180_4_5
    · exact s180_4_6
    · exact s180_4_7
  · fin_cases v
    · exact s180_5_0
    · exact s180_5_1
    · exact s180_5_2
    · exact s180_5_3
    · exact s180_5_4
    · exact s180_5_5
    · exact s180_5_6
    · exact s180_5_7
  · fin_cases v
    · exact s180_6_0
    · exact s180_6_1
    · exact s180_6_2
    · exact s180_6_3
    · exact s180_6_4
    · exact s180_6_5
    · exact s180_6_6
    · exact s180_6_7
  · exact List.all_eq_true.mp col180_7 v (List.mem_finRange v)
theorem col181_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 0 v) = true := by decide +kernel
theorem col181_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 1 v) = true := by decide +kernel
theorem col181_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 2 v) = true := by decide +kernel
theorem s181_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 0 = true := by decide +kernel
theorem s181_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 1 = true := by decide +kernel
theorem s181_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 2 = true := by decide +kernel
theorem k181_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k181_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k181_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s181_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k181_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k181_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k181_3_3_26 k h.1 (by omega)
theorem s181_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 4 = true := by decide +kernel
theorem s181_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 5 = true := by decide +kernel
theorem k181_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k181_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k181_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k181_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k181_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k181_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k181_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k181_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k181_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k181_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k181_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s181_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k181_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k181_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k181_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k181_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k181_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k181_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k181_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k181_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k181_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k181_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k181_3_6_130 k h.1 (by omega)
theorem s181_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 3 7 = true := by decide +kernel
theorem s181_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 0 = true := by decide +kernel
theorem s181_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 1 = true := by decide +kernel
theorem s181_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 2 = true := by decide +kernel
theorem s181_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 3 = true := by decide +kernel
theorem s181_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 4 = true := by decide +kernel
theorem s181_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 5 = true := by decide +kernel
theorem k181_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k181_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k181_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k181_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k181_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k181_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k181_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s181_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k181_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k181_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k181_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k181_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k181_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k181_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k181_4_6_126 k h.1 (by omega)
theorem s181_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 4 7 = true := by decide +kernel
theorem s181_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 0 = true := by decide +kernel
theorem s181_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 1 = true := by decide +kernel
theorem s181_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 2 = true := by decide +kernel
theorem s181_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 3 = true := by decide +kernel
theorem s181_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 4 = true := by decide +kernel
theorem s181_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 5 = true := by decide +kernel
theorem k181_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k181_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k181_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k181_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k181_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k181_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k181_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s181_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k181_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k181_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k181_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k181_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k181_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k181_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 181) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (181 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k181_5_6_126 k h.1 (by omega)
theorem s181_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 5 7 = true := by decide +kernel
theorem s181_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 0 = true := by decide +kernel
theorem s181_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 1 = true := by decide +kernel
theorem s181_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 2 = true := by decide +kernel
theorem s181_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 3 = true := by decide +kernel
theorem s181_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 4 = true := by decide +kernel
theorem s181_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 5 = true := by decide +kernel
theorem s181_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 6 = true := by decide +kernel
theorem k181_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k181_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k181_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k181_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k181_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s181_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k181_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k181_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k181_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k181_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 181) ((InDA1.TCasaD 6 6 7).getD (181 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k181_6_7_12 k h.1 (by omega)
theorem col181_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 7 v) = true := by decide +kernel
theorem col181 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 181) 181 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col181_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col181_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col181_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s181_3_0
    · exact s181_3_1
    · exact s181_3_2
    · exact s181_3_3
    · exact s181_3_4
    · exact s181_3_5
    · exact s181_3_6
    · exact s181_3_7
  · fin_cases v
    · exact s181_4_0
    · exact s181_4_1
    · exact s181_4_2
    · exact s181_4_3
    · exact s181_4_4
    · exact s181_4_5
    · exact s181_4_6
    · exact s181_4_7
  · fin_cases v
    · exact s181_5_0
    · exact s181_5_1
    · exact s181_5_2
    · exact s181_5_3
    · exact s181_5_4
    · exact s181_5_5
    · exact s181_5_6
    · exact s181_5_7
  · fin_cases v
    · exact s181_6_0
    · exact s181_6_1
    · exact s181_6_2
    · exact s181_6_3
    · exact s181_6_4
    · exact s181_6_5
    · exact s181_6_6
    · exact s181_6_7
  · exact List.all_eq_true.mp col181_7 v (List.mem_finRange v)
theorem col182_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 0 v) = true := by decide +kernel
theorem col182_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 1 v) = true := by decide +kernel
theorem col182_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 2 v) = true := by decide +kernel
theorem s182_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 0 = true := by decide +kernel
theorem s182_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 1 = true := by decide +kernel
theorem s182_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 2 = true := by decide +kernel
theorem k182_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k182_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k182_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s182_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k182_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k182_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k182_3_3_26 k h.1 (by omega)
theorem s182_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 4 = true := by decide +kernel
theorem s182_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 5 = true := by decide +kernel
theorem k182_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k182_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k182_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k182_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k182_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k182_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k182_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k182_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k182_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k182_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k182_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s182_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k182_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k182_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k182_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k182_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k182_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k182_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k182_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k182_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k182_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k182_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k182_3_6_130 k h.1 (by omega)
theorem s182_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 3 7 = true := by decide +kernel
theorem s182_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 0 = true := by decide +kernel
theorem s182_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 1 = true := by decide +kernel
theorem s182_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 2 = true := by decide +kernel
theorem s182_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 3 = true := by decide +kernel
theorem s182_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 4 = true := by decide +kernel
theorem s182_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 5 = true := by decide +kernel
theorem k182_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k182_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k182_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k182_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k182_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k182_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k182_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s182_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k182_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k182_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k182_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k182_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k182_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k182_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k182_4_6_126 k h.1 (by omega)
theorem s182_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 4 7 = true := by decide +kernel
theorem s182_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 0 = true := by decide +kernel
theorem s182_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 1 = true := by decide +kernel
theorem s182_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 2 = true := by decide +kernel
theorem s182_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 3 = true := by decide +kernel
theorem s182_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 4 = true := by decide +kernel
theorem s182_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 5 = true := by decide +kernel
theorem k182_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k182_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k182_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k182_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k182_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k182_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k182_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s182_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k182_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k182_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k182_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k182_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k182_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k182_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 182) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (182 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k182_5_6_126 k h.1 (by omega)
theorem s182_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 5 7 = true := by decide +kernel
theorem s182_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 0 = true := by decide +kernel
theorem s182_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 1 = true := by decide +kernel
theorem s182_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 2 = true := by decide +kernel
theorem s182_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 3 = true := by decide +kernel
theorem s182_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 4 = true := by decide +kernel
theorem s182_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 5 = true := by decide +kernel
theorem s182_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 6 = true := by decide +kernel
theorem k182_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k182_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k182_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k182_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k182_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s182_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k182_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k182_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k182_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k182_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 182) ((InDA1.TCasaD 6 6 7).getD (182 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k182_6_7_12 k h.1 (by omega)
theorem col182_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 7 v) = true := by decide +kernel
theorem col182 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 182) 182 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col182_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col182_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col182_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s182_3_0
    · exact s182_3_1
    · exact s182_3_2
    · exact s182_3_3
    · exact s182_3_4
    · exact s182_3_5
    · exact s182_3_6
    · exact s182_3_7
  · fin_cases v
    · exact s182_4_0
    · exact s182_4_1
    · exact s182_4_2
    · exact s182_4_3
    · exact s182_4_4
    · exact s182_4_5
    · exact s182_4_6
    · exact s182_4_7
  · fin_cases v
    · exact s182_5_0
    · exact s182_5_1
    · exact s182_5_2
    · exact s182_5_3
    · exact s182_5_4
    · exact s182_5_5
    · exact s182_5_6
    · exact s182_5_7
  · fin_cases v
    · exact s182_6_0
    · exact s182_6_1
    · exact s182_6_2
    · exact s182_6_3
    · exact s182_6_4
    · exact s182_6_5
    · exact s182_6_6
    · exact s182_6_7
  · exact List.all_eq_true.mp col182_7 v (List.mem_finRange v)
theorem col183_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 0 v) = true := by decide +kernel
theorem col183_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 1 v) = true := by decide +kernel
theorem col183_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 2 v) = true := by decide +kernel
theorem s183_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 0 = true := by decide +kernel
theorem s183_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 1 = true := by decide +kernel
theorem s183_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 2 = true := by decide +kernel
theorem k183_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k183_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k183_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s183_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k183_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k183_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k183_3_3_26 k h.1 (by omega)
theorem s183_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 4 = true := by decide +kernel
theorem s183_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 5 = true := by decide +kernel
theorem k183_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k183_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k183_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k183_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k183_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k183_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k183_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k183_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k183_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k183_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k183_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s183_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k183_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k183_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k183_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k183_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k183_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k183_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k183_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k183_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k183_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k183_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k183_3_6_130 k h.1 (by omega)
theorem s183_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 3 7 = true := by decide +kernel
theorem s183_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 0 = true := by decide +kernel
theorem s183_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 1 = true := by decide +kernel
theorem s183_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 2 = true := by decide +kernel
theorem s183_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 3 = true := by decide +kernel
theorem s183_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 4 = true := by decide +kernel
theorem s183_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 5 = true := by decide +kernel
theorem k183_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k183_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k183_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k183_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k183_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k183_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k183_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s183_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k183_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k183_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k183_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k183_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k183_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k183_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k183_4_6_126 k h.1 (by omega)
theorem s183_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 4 7 = true := by decide +kernel
theorem s183_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 0 = true := by decide +kernel
theorem s183_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 1 = true := by decide +kernel
theorem s183_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 2 = true := by decide +kernel
theorem s183_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 3 = true := by decide +kernel
theorem s183_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 4 = true := by decide +kernel
theorem s183_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 5 = true := by decide +kernel
theorem k183_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k183_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k183_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k183_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k183_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k183_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k183_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s183_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k183_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k183_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k183_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k183_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k183_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k183_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 183) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (183 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k183_5_6_126 k h.1 (by omega)
theorem s183_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 5 7 = true := by decide +kernel
theorem s183_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 0 = true := by decide +kernel
theorem s183_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 1 = true := by decide +kernel
theorem s183_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 2 = true := by decide +kernel
theorem s183_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 3 = true := by decide +kernel
theorem s183_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 4 = true := by decide +kernel
theorem s183_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 5 = true := by decide +kernel
theorem s183_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 6 = true := by decide +kernel
theorem k183_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k183_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k183_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k183_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k183_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s183_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k183_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k183_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k183_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k183_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 183) ((InDA1.TCasaD 6 6 7).getD (183 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k183_6_7_12 k h.1 (by omega)
theorem col183_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 7 v) = true := by decide +kernel
theorem col183 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 183) 183 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col183_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col183_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col183_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s183_3_0
    · exact s183_3_1
    · exact s183_3_2
    · exact s183_3_3
    · exact s183_3_4
    · exact s183_3_5
    · exact s183_3_6
    · exact s183_3_7
  · fin_cases v
    · exact s183_4_0
    · exact s183_4_1
    · exact s183_4_2
    · exact s183_4_3
    · exact s183_4_4
    · exact s183_4_5
    · exact s183_4_6
    · exact s183_4_7
  · fin_cases v
    · exact s183_5_0
    · exact s183_5_1
    · exact s183_5_2
    · exact s183_5_3
    · exact s183_5_4
    · exact s183_5_5
    · exact s183_5_6
    · exact s183_5_7
  · fin_cases v
    · exact s183_6_0
    · exact s183_6_1
    · exact s183_6_2
    · exact s183_6_3
    · exact s183_6_4
    · exact s183_6_5
    · exact s183_6_6
    · exact s183_6_7
  · exact List.all_eq_true.mp col183_7 v (List.mem_finRange v)
theorem col184_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 0 v) = true := by decide +kernel
theorem col184_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 1 v) = true := by decide +kernel
theorem col184_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 2 v) = true := by decide +kernel
theorem s184_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 0 = true := by decide +kernel
theorem s184_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 1 = true := by decide +kernel
theorem s184_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 2 = true := by decide +kernel
theorem k184_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k184_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k184_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s184_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k184_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k184_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k184_3_3_26 k h.1 (by omega)
theorem s184_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 4 = true := by decide +kernel
theorem s184_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 5 = true := by decide +kernel
theorem k184_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k184_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k184_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k184_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k184_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k184_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k184_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k184_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k184_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k184_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k184_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s184_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k184_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k184_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k184_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k184_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k184_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k184_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k184_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k184_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k184_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k184_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k184_3_6_130 k h.1 (by omega)
theorem s184_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 3 7 = true := by decide +kernel
theorem s184_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 0 = true := by decide +kernel
theorem s184_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 1 = true := by decide +kernel
theorem s184_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 2 = true := by decide +kernel
theorem s184_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 3 = true := by decide +kernel
theorem s184_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 4 = true := by decide +kernel
theorem s184_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 5 = true := by decide +kernel
theorem k184_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k184_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k184_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k184_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k184_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k184_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k184_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s184_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k184_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k184_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k184_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k184_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k184_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k184_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k184_4_6_126 k h.1 (by omega)
theorem s184_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 4 7 = true := by decide +kernel
theorem s184_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 0 = true := by decide +kernel
theorem s184_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 1 = true := by decide +kernel
theorem s184_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 2 = true := by decide +kernel
theorem s184_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 3 = true := by decide +kernel
theorem s184_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 4 = true := by decide +kernel
theorem s184_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 5 = true := by decide +kernel
theorem k184_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k184_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k184_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k184_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k184_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k184_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k184_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s184_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k184_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k184_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k184_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k184_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k184_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k184_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 184) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (184 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k184_5_6_126 k h.1 (by omega)
theorem s184_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 5 7 = true := by decide +kernel
theorem s184_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 0 = true := by decide +kernel
theorem s184_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 1 = true := by decide +kernel
theorem s184_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 2 = true := by decide +kernel
theorem s184_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 3 = true := by decide +kernel
theorem s184_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 4 = true := by decide +kernel
theorem s184_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 5 = true := by decide +kernel
theorem s184_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 6 = true := by decide +kernel
theorem k184_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k184_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k184_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k184_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k184_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s184_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k184_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k184_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k184_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k184_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 184) ((InDA1.TCasaD 6 6 7).getD (184 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k184_6_7_12 k h.1 (by omega)
theorem col184_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 7 v) = true := by decide +kernel
theorem col184 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 184) 184 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col184_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col184_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col184_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s184_3_0
    · exact s184_3_1
    · exact s184_3_2
    · exact s184_3_3
    · exact s184_3_4
    · exact s184_3_5
    · exact s184_3_6
    · exact s184_3_7
  · fin_cases v
    · exact s184_4_0
    · exact s184_4_1
    · exact s184_4_2
    · exact s184_4_3
    · exact s184_4_4
    · exact s184_4_5
    · exact s184_4_6
    · exact s184_4_7
  · fin_cases v
    · exact s184_5_0
    · exact s184_5_1
    · exact s184_5_2
    · exact s184_5_3
    · exact s184_5_4
    · exact s184_5_5
    · exact s184_5_6
    · exact s184_5_7
  · fin_cases v
    · exact s184_6_0
    · exact s184_6_1
    · exact s184_6_2
    · exact s184_6_3
    · exact s184_6_4
    · exact s184_6_5
    · exact s184_6_6
    · exact s184_6_7
  · exact List.all_eq_true.mp col184_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
