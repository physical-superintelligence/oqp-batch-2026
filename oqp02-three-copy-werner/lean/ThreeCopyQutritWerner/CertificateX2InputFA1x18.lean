module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [90, 95). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col90_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 0 v) = true := by decide +kernel
theorem col90_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 1 v) = true := by decide +kernel
theorem col90_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 2 v) = true := by decide +kernel
theorem s90_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 0 = true := by decide +kernel
theorem s90_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 1 = true := by decide +kernel
theorem s90_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 2 = true := by decide +kernel
theorem k90_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k90_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k90_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s90_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k90_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k90_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k90_3_3_26 k h.1 (by omega)
theorem s90_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 4 = true := by decide +kernel
theorem s90_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 5 = true := by decide +kernel
theorem k90_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k90_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k90_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k90_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k90_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k90_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k90_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k90_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k90_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k90_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k90_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s90_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k90_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k90_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k90_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k90_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k90_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k90_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k90_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k90_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k90_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k90_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k90_3_6_130 k h.1 (by omega)
theorem s90_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 3 7 = true := by decide +kernel
theorem s90_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 0 = true := by decide +kernel
theorem s90_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 1 = true := by decide +kernel
theorem s90_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 2 = true := by decide +kernel
theorem s90_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 3 = true := by decide +kernel
theorem s90_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 4 = true := by decide +kernel
theorem s90_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 5 = true := by decide +kernel
theorem k90_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k90_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k90_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k90_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k90_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k90_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k90_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s90_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k90_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k90_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k90_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k90_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k90_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k90_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k90_4_6_126 k h.1 (by omega)
theorem s90_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 4 7 = true := by decide +kernel
theorem s90_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 0 = true := by decide +kernel
theorem s90_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 1 = true := by decide +kernel
theorem s90_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 2 = true := by decide +kernel
theorem s90_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 3 = true := by decide +kernel
theorem s90_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 4 = true := by decide +kernel
theorem s90_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 5 = true := by decide +kernel
theorem k90_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k90_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k90_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k90_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k90_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k90_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k90_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s90_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k90_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k90_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k90_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k90_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k90_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k90_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 90) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (90 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k90_5_6_126 k h.1 (by omega)
theorem s90_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 5 7 = true := by decide +kernel
theorem s90_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 0 = true := by decide +kernel
theorem s90_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 1 = true := by decide +kernel
theorem s90_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 2 = true := by decide +kernel
theorem s90_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 3 = true := by decide +kernel
theorem s90_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 4 = true := by decide +kernel
theorem s90_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 5 = true := by decide +kernel
theorem s90_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 6 = true := by decide +kernel
theorem k90_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k90_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k90_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k90_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k90_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s90_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k90_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k90_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k90_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k90_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 90) ((InDA1.TCasaD 6 6 7).getD (90 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k90_6_7_12 k h.1 (by omega)
theorem col90_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 7 v) = true := by decide +kernel
theorem col90 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 90) 90 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col90_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col90_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col90_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s90_3_0
    · exact s90_3_1
    · exact s90_3_2
    · exact s90_3_3
    · exact s90_3_4
    · exact s90_3_5
    · exact s90_3_6
    · exact s90_3_7
  · fin_cases v
    · exact s90_4_0
    · exact s90_4_1
    · exact s90_4_2
    · exact s90_4_3
    · exact s90_4_4
    · exact s90_4_5
    · exact s90_4_6
    · exact s90_4_7
  · fin_cases v
    · exact s90_5_0
    · exact s90_5_1
    · exact s90_5_2
    · exact s90_5_3
    · exact s90_5_4
    · exact s90_5_5
    · exact s90_5_6
    · exact s90_5_7
  · fin_cases v
    · exact s90_6_0
    · exact s90_6_1
    · exact s90_6_2
    · exact s90_6_3
    · exact s90_6_4
    · exact s90_6_5
    · exact s90_6_6
    · exact s90_6_7
  · exact List.all_eq_true.mp col90_7 v (List.mem_finRange v)
theorem col91_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 0 v) = true := by decide +kernel
theorem col91_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 1 v) = true := by decide +kernel
theorem col91_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 2 v) = true := by decide +kernel
theorem s91_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 0 = true := by decide +kernel
theorem s91_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 1 = true := by decide +kernel
theorem s91_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 2 = true := by decide +kernel
theorem k91_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k91_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k91_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s91_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k91_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k91_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k91_3_3_26 k h.1 (by omega)
theorem s91_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 4 = true := by decide +kernel
theorem s91_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 5 = true := by decide +kernel
theorem k91_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k91_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k91_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k91_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k91_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k91_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k91_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k91_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k91_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k91_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k91_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s91_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k91_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k91_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k91_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k91_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k91_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k91_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k91_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k91_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k91_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k91_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k91_3_6_130 k h.1 (by omega)
theorem s91_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 3 7 = true := by decide +kernel
theorem s91_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 0 = true := by decide +kernel
theorem s91_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 1 = true := by decide +kernel
theorem s91_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 2 = true := by decide +kernel
theorem s91_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 3 = true := by decide +kernel
theorem s91_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 4 = true := by decide +kernel
theorem s91_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 5 = true := by decide +kernel
theorem k91_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k91_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k91_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k91_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k91_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k91_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k91_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s91_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k91_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k91_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k91_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k91_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k91_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k91_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k91_4_6_126 k h.1 (by omega)
theorem s91_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 4 7 = true := by decide +kernel
theorem s91_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 0 = true := by decide +kernel
theorem s91_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 1 = true := by decide +kernel
theorem s91_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 2 = true := by decide +kernel
theorem s91_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 3 = true := by decide +kernel
theorem s91_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 4 = true := by decide +kernel
theorem s91_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 5 = true := by decide +kernel
theorem k91_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k91_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k91_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k91_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k91_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k91_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k91_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s91_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k91_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k91_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k91_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k91_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k91_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k91_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 91) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (91 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k91_5_6_126 k h.1 (by omega)
theorem s91_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 5 7 = true := by decide +kernel
theorem s91_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 0 = true := by decide +kernel
theorem s91_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 1 = true := by decide +kernel
theorem s91_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 2 = true := by decide +kernel
theorem s91_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 3 = true := by decide +kernel
theorem s91_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 4 = true := by decide +kernel
theorem s91_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 5 = true := by decide +kernel
theorem s91_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 6 = true := by decide +kernel
theorem k91_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k91_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k91_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k91_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k91_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s91_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k91_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k91_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k91_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k91_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 91) ((InDA1.TCasaD 6 6 7).getD (91 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k91_6_7_12 k h.1 (by omega)
theorem col91_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 7 v) = true := by decide +kernel
theorem col91 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 91) 91 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col91_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col91_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col91_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s91_3_0
    · exact s91_3_1
    · exact s91_3_2
    · exact s91_3_3
    · exact s91_3_4
    · exact s91_3_5
    · exact s91_3_6
    · exact s91_3_7
  · fin_cases v
    · exact s91_4_0
    · exact s91_4_1
    · exact s91_4_2
    · exact s91_4_3
    · exact s91_4_4
    · exact s91_4_5
    · exact s91_4_6
    · exact s91_4_7
  · fin_cases v
    · exact s91_5_0
    · exact s91_5_1
    · exact s91_5_2
    · exact s91_5_3
    · exact s91_5_4
    · exact s91_5_5
    · exact s91_5_6
    · exact s91_5_7
  · fin_cases v
    · exact s91_6_0
    · exact s91_6_1
    · exact s91_6_2
    · exact s91_6_3
    · exact s91_6_4
    · exact s91_6_5
    · exact s91_6_6
    · exact s91_6_7
  · exact List.all_eq_true.mp col91_7 v (List.mem_finRange v)
theorem col92_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 0 v) = true := by decide +kernel
theorem col92_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 1 v) = true := by decide +kernel
theorem col92_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 2 v) = true := by decide +kernel
theorem s92_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 0 = true := by decide +kernel
theorem s92_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 1 = true := by decide +kernel
theorem s92_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 2 = true := by decide +kernel
theorem k92_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k92_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k92_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s92_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k92_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k92_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k92_3_3_26 k h.1 (by omega)
theorem s92_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 4 = true := by decide +kernel
theorem s92_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 5 = true := by decide +kernel
theorem k92_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k92_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k92_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k92_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k92_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k92_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k92_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k92_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k92_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k92_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k92_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s92_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k92_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k92_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k92_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k92_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k92_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k92_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k92_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k92_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k92_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k92_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k92_3_6_130 k h.1 (by omega)
theorem s92_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 3 7 = true := by decide +kernel
theorem s92_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 0 = true := by decide +kernel
theorem s92_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 1 = true := by decide +kernel
theorem s92_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 2 = true := by decide +kernel
theorem s92_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 3 = true := by decide +kernel
theorem s92_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 4 = true := by decide +kernel
theorem s92_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 5 = true := by decide +kernel
theorem k92_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k92_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k92_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k92_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k92_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k92_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k92_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s92_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k92_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k92_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k92_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k92_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k92_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k92_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k92_4_6_126 k h.1 (by omega)
theorem s92_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 4 7 = true := by decide +kernel
theorem s92_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 0 = true := by decide +kernel
theorem s92_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 1 = true := by decide +kernel
theorem s92_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 2 = true := by decide +kernel
theorem s92_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 3 = true := by decide +kernel
theorem s92_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 4 = true := by decide +kernel
theorem s92_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 5 = true := by decide +kernel
theorem k92_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k92_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k92_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k92_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k92_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k92_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k92_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s92_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k92_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k92_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k92_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k92_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k92_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k92_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 92) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (92 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k92_5_6_126 k h.1 (by omega)
theorem s92_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 5 7 = true := by decide +kernel
theorem s92_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 0 = true := by decide +kernel
theorem s92_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 1 = true := by decide +kernel
theorem s92_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 2 = true := by decide +kernel
theorem s92_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 3 = true := by decide +kernel
theorem s92_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 4 = true := by decide +kernel
theorem s92_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 5 = true := by decide +kernel
theorem s92_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 6 = true := by decide +kernel
theorem k92_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k92_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k92_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k92_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k92_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s92_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k92_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k92_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k92_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k92_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 92) ((InDA1.TCasaD 6 6 7).getD (92 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k92_6_7_12 k h.1 (by omega)
theorem col92_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 7 v) = true := by decide +kernel
theorem col92 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 92) 92 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col92_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col92_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col92_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s92_3_0
    · exact s92_3_1
    · exact s92_3_2
    · exact s92_3_3
    · exact s92_3_4
    · exact s92_3_5
    · exact s92_3_6
    · exact s92_3_7
  · fin_cases v
    · exact s92_4_0
    · exact s92_4_1
    · exact s92_4_2
    · exact s92_4_3
    · exact s92_4_4
    · exact s92_4_5
    · exact s92_4_6
    · exact s92_4_7
  · fin_cases v
    · exact s92_5_0
    · exact s92_5_1
    · exact s92_5_2
    · exact s92_5_3
    · exact s92_5_4
    · exact s92_5_5
    · exact s92_5_6
    · exact s92_5_7
  · fin_cases v
    · exact s92_6_0
    · exact s92_6_1
    · exact s92_6_2
    · exact s92_6_3
    · exact s92_6_4
    · exact s92_6_5
    · exact s92_6_6
    · exact s92_6_7
  · exact List.all_eq_true.mp col92_7 v (List.mem_finRange v)
theorem col93_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 0 v) = true := by decide +kernel
theorem col93_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 1 v) = true := by decide +kernel
theorem col93_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 2 v) = true := by decide +kernel
theorem s93_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 0 = true := by decide +kernel
theorem s93_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 1 = true := by decide +kernel
theorem s93_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 2 = true := by decide +kernel
theorem k93_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k93_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k93_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s93_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k93_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k93_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k93_3_3_26 k h.1 (by omega)
theorem s93_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 4 = true := by decide +kernel
theorem s93_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 5 = true := by decide +kernel
theorem k93_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k93_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k93_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k93_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k93_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k93_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k93_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k93_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k93_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k93_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k93_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s93_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k93_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k93_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k93_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k93_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k93_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k93_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k93_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k93_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k93_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k93_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k93_3_6_130 k h.1 (by omega)
theorem s93_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 3 7 = true := by decide +kernel
theorem s93_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 0 = true := by decide +kernel
theorem s93_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 1 = true := by decide +kernel
theorem s93_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 2 = true := by decide +kernel
theorem s93_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 3 = true := by decide +kernel
theorem s93_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 4 = true := by decide +kernel
theorem s93_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 5 = true := by decide +kernel
theorem k93_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k93_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k93_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k93_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k93_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k93_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k93_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s93_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k93_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k93_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k93_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k93_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k93_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k93_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k93_4_6_126 k h.1 (by omega)
theorem s93_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 4 7 = true := by decide +kernel
theorem s93_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 0 = true := by decide +kernel
theorem s93_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 1 = true := by decide +kernel
theorem s93_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 2 = true := by decide +kernel
theorem s93_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 3 = true := by decide +kernel
theorem s93_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 4 = true := by decide +kernel
theorem s93_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 5 = true := by decide +kernel
theorem k93_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k93_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k93_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k93_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k93_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k93_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k93_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s93_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k93_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k93_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k93_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k93_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k93_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k93_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 93) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (93 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k93_5_6_126 k h.1 (by omega)
theorem s93_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 5 7 = true := by decide +kernel
theorem s93_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 0 = true := by decide +kernel
theorem s93_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 1 = true := by decide +kernel
theorem s93_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 2 = true := by decide +kernel
theorem s93_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 3 = true := by decide +kernel
theorem s93_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 4 = true := by decide +kernel
theorem s93_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 5 = true := by decide +kernel
theorem s93_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 6 = true := by decide +kernel
theorem k93_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k93_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k93_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k93_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k93_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s93_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k93_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k93_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k93_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k93_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 93) ((InDA1.TCasaD 6 6 7).getD (93 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k93_6_7_12 k h.1 (by omega)
theorem col93_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 7 v) = true := by decide +kernel
theorem col93 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 93) 93 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col93_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col93_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col93_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s93_3_0
    · exact s93_3_1
    · exact s93_3_2
    · exact s93_3_3
    · exact s93_3_4
    · exact s93_3_5
    · exact s93_3_6
    · exact s93_3_7
  · fin_cases v
    · exact s93_4_0
    · exact s93_4_1
    · exact s93_4_2
    · exact s93_4_3
    · exact s93_4_4
    · exact s93_4_5
    · exact s93_4_6
    · exact s93_4_7
  · fin_cases v
    · exact s93_5_0
    · exact s93_5_1
    · exact s93_5_2
    · exact s93_5_3
    · exact s93_5_4
    · exact s93_5_5
    · exact s93_5_6
    · exact s93_5_7
  · fin_cases v
    · exact s93_6_0
    · exact s93_6_1
    · exact s93_6_2
    · exact s93_6_3
    · exact s93_6_4
    · exact s93_6_5
    · exact s93_6_6
    · exact s93_6_7
  · exact List.all_eq_true.mp col93_7 v (List.mem_finRange v)
theorem col94_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 0 v) = true := by decide +kernel
theorem col94_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 1 v) = true := by decide +kernel
theorem col94_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 2 v) = true := by decide +kernel
theorem s94_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 0 = true := by decide +kernel
theorem s94_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 1 = true := by decide +kernel
theorem s94_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 2 = true := by decide +kernel
theorem k94_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k94_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k94_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s94_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k94_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k94_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k94_3_3_26 k h.1 (by omega)
theorem s94_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 4 = true := by decide +kernel
theorem s94_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 5 = true := by decide +kernel
theorem k94_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k94_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k94_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k94_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k94_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k94_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k94_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k94_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k94_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k94_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k94_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s94_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k94_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k94_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k94_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k94_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k94_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k94_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k94_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k94_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k94_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k94_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k94_3_6_130 k h.1 (by omega)
theorem s94_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 3 7 = true := by decide +kernel
theorem s94_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 0 = true := by decide +kernel
theorem s94_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 1 = true := by decide +kernel
theorem s94_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 2 = true := by decide +kernel
theorem s94_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 3 = true := by decide +kernel
theorem s94_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 4 = true := by decide +kernel
theorem s94_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 5 = true := by decide +kernel
theorem k94_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k94_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k94_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k94_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k94_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k94_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k94_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s94_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k94_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k94_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k94_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k94_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k94_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k94_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k94_4_6_126 k h.1 (by omega)
theorem s94_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 4 7 = true := by decide +kernel
theorem s94_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 0 = true := by decide +kernel
theorem s94_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 1 = true := by decide +kernel
theorem s94_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 2 = true := by decide +kernel
theorem s94_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 3 = true := by decide +kernel
theorem s94_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 4 = true := by decide +kernel
theorem s94_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 5 = true := by decide +kernel
theorem k94_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k94_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k94_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k94_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k94_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k94_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k94_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s94_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k94_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k94_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k94_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k94_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k94_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k94_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 94) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (94 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k94_5_6_126 k h.1 (by omega)
theorem s94_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 5 7 = true := by decide +kernel
theorem s94_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 0 = true := by decide +kernel
theorem s94_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 1 = true := by decide +kernel
theorem s94_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 2 = true := by decide +kernel
theorem s94_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 3 = true := by decide +kernel
theorem s94_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 4 = true := by decide +kernel
theorem s94_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 5 = true := by decide +kernel
theorem s94_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 6 = true := by decide +kernel
theorem k94_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k94_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k94_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k94_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k94_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s94_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k94_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k94_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k94_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k94_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 94) ((InDA1.TCasaD 6 6 7).getD (94 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k94_6_7_12 k h.1 (by omega)
theorem col94_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 7 v) = true := by decide +kernel
theorem col94 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 94) 94 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col94_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col94_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col94_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s94_3_0
    · exact s94_3_1
    · exact s94_3_2
    · exact s94_3_3
    · exact s94_3_4
    · exact s94_3_5
    · exact s94_3_6
    · exact s94_3_7
  · fin_cases v
    · exact s94_4_0
    · exact s94_4_1
    · exact s94_4_2
    · exact s94_4_3
    · exact s94_4_4
    · exact s94_4_5
    · exact s94_4_6
    · exact s94_4_7
  · fin_cases v
    · exact s94_5_0
    · exact s94_5_1
    · exact s94_5_2
    · exact s94_5_3
    · exact s94_5_4
    · exact s94_5_5
    · exact s94_5_6
    · exact s94_5_7
  · fin_cases v
    · exact s94_6_0
    · exact s94_6_1
    · exact s94_6_2
    · exact s94_6_3
    · exact s94_6_4
    · exact s94_6_5
    · exact s94_6_6
    · exact s94_6_7
  · exact List.all_eq_true.mp col94_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
