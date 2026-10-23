module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [115, 120). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col115_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 0 v) = true := by decide +kernel
theorem col115_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 1 v) = true := by decide +kernel
theorem col115_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 2 v) = true := by decide +kernel
theorem s115_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 0 = true := by decide +kernel
theorem s115_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 1 = true := by decide +kernel
theorem s115_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 2 = true := by decide +kernel
theorem k115_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k115_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k115_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s115_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k115_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k115_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k115_3_3_26 k h.1 (by omega)
theorem s115_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 4 = true := by decide +kernel
theorem s115_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 5 = true := by decide +kernel
theorem k115_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k115_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k115_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k115_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k115_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k115_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k115_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k115_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k115_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k115_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k115_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s115_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k115_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k115_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k115_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k115_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k115_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k115_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k115_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k115_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k115_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k115_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k115_3_6_130 k h.1 (by omega)
theorem s115_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 3 7 = true := by decide +kernel
theorem s115_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 0 = true := by decide +kernel
theorem s115_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 1 = true := by decide +kernel
theorem s115_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 2 = true := by decide +kernel
theorem s115_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 3 = true := by decide +kernel
theorem s115_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 4 = true := by decide +kernel
theorem s115_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 5 = true := by decide +kernel
theorem k115_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k115_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k115_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k115_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k115_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k115_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k115_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s115_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k115_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k115_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k115_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k115_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k115_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k115_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k115_4_6_126 k h.1 (by omega)
theorem s115_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 4 7 = true := by decide +kernel
theorem s115_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 0 = true := by decide +kernel
theorem s115_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 1 = true := by decide +kernel
theorem s115_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 2 = true := by decide +kernel
theorem s115_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 3 = true := by decide +kernel
theorem s115_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 4 = true := by decide +kernel
theorem s115_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 5 = true := by decide +kernel
theorem k115_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k115_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k115_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k115_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k115_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k115_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k115_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s115_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k115_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k115_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k115_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k115_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k115_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k115_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 115) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (115 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k115_5_6_126 k h.1 (by omega)
theorem s115_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 5 7 = true := by decide +kernel
theorem s115_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 0 = true := by decide +kernel
theorem s115_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 1 = true := by decide +kernel
theorem s115_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 2 = true := by decide +kernel
theorem s115_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 3 = true := by decide +kernel
theorem s115_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 4 = true := by decide +kernel
theorem s115_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 5 = true := by decide +kernel
theorem s115_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 6 = true := by decide +kernel
theorem k115_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k115_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k115_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k115_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k115_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s115_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k115_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k115_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k115_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k115_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 115) ((InDA1.TCasaD 6 6 7).getD (115 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k115_6_7_12 k h.1 (by omega)
theorem col115_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 7 v) = true := by decide +kernel
theorem col115 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 115) 115 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col115_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col115_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col115_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s115_3_0
    · exact s115_3_1
    · exact s115_3_2
    · exact s115_3_3
    · exact s115_3_4
    · exact s115_3_5
    · exact s115_3_6
    · exact s115_3_7
  · fin_cases v
    · exact s115_4_0
    · exact s115_4_1
    · exact s115_4_2
    · exact s115_4_3
    · exact s115_4_4
    · exact s115_4_5
    · exact s115_4_6
    · exact s115_4_7
  · fin_cases v
    · exact s115_5_0
    · exact s115_5_1
    · exact s115_5_2
    · exact s115_5_3
    · exact s115_5_4
    · exact s115_5_5
    · exact s115_5_6
    · exact s115_5_7
  · fin_cases v
    · exact s115_6_0
    · exact s115_6_1
    · exact s115_6_2
    · exact s115_6_3
    · exact s115_6_4
    · exact s115_6_5
    · exact s115_6_6
    · exact s115_6_7
  · exact List.all_eq_true.mp col115_7 v (List.mem_finRange v)
theorem col116_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 0 v) = true := by decide +kernel
theorem col116_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 1 v) = true := by decide +kernel
theorem col116_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 2 v) = true := by decide +kernel
theorem s116_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 0 = true := by decide +kernel
theorem s116_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 1 = true := by decide +kernel
theorem s116_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 2 = true := by decide +kernel
theorem k116_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k116_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k116_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s116_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k116_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k116_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k116_3_3_26 k h.1 (by omega)
theorem s116_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 4 = true := by decide +kernel
theorem s116_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 5 = true := by decide +kernel
theorem k116_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k116_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k116_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k116_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k116_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k116_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k116_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k116_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k116_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k116_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k116_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s116_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k116_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k116_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k116_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k116_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k116_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k116_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k116_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k116_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k116_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k116_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k116_3_6_130 k h.1 (by omega)
theorem s116_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 3 7 = true := by decide +kernel
theorem s116_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 0 = true := by decide +kernel
theorem s116_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 1 = true := by decide +kernel
theorem s116_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 2 = true := by decide +kernel
theorem s116_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 3 = true := by decide +kernel
theorem s116_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 4 = true := by decide +kernel
theorem s116_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 5 = true := by decide +kernel
theorem k116_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k116_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k116_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k116_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k116_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k116_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k116_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s116_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k116_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k116_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k116_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k116_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k116_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k116_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k116_4_6_126 k h.1 (by omega)
theorem s116_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 4 7 = true := by decide +kernel
theorem s116_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 0 = true := by decide +kernel
theorem s116_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 1 = true := by decide +kernel
theorem s116_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 2 = true := by decide +kernel
theorem s116_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 3 = true := by decide +kernel
theorem s116_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 4 = true := by decide +kernel
theorem s116_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 5 = true := by decide +kernel
theorem k116_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k116_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k116_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k116_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k116_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k116_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k116_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s116_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k116_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k116_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k116_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k116_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k116_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k116_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 116) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (116 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k116_5_6_126 k h.1 (by omega)
theorem s116_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 5 7 = true := by decide +kernel
theorem s116_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 0 = true := by decide +kernel
theorem s116_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 1 = true := by decide +kernel
theorem s116_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 2 = true := by decide +kernel
theorem s116_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 3 = true := by decide +kernel
theorem s116_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 4 = true := by decide +kernel
theorem s116_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 5 = true := by decide +kernel
theorem s116_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 6 = true := by decide +kernel
theorem k116_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k116_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k116_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k116_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k116_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s116_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k116_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k116_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k116_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k116_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 116) ((InDA1.TCasaD 6 6 7).getD (116 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k116_6_7_12 k h.1 (by omega)
theorem col116_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 7 v) = true := by decide +kernel
theorem col116 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 116) 116 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col116_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col116_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col116_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s116_3_0
    · exact s116_3_1
    · exact s116_3_2
    · exact s116_3_3
    · exact s116_3_4
    · exact s116_3_5
    · exact s116_3_6
    · exact s116_3_7
  · fin_cases v
    · exact s116_4_0
    · exact s116_4_1
    · exact s116_4_2
    · exact s116_4_3
    · exact s116_4_4
    · exact s116_4_5
    · exact s116_4_6
    · exact s116_4_7
  · fin_cases v
    · exact s116_5_0
    · exact s116_5_1
    · exact s116_5_2
    · exact s116_5_3
    · exact s116_5_4
    · exact s116_5_5
    · exact s116_5_6
    · exact s116_5_7
  · fin_cases v
    · exact s116_6_0
    · exact s116_6_1
    · exact s116_6_2
    · exact s116_6_3
    · exact s116_6_4
    · exact s116_6_5
    · exact s116_6_6
    · exact s116_6_7
  · exact List.all_eq_true.mp col116_7 v (List.mem_finRange v)
theorem col117_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 0 v) = true := by decide +kernel
theorem col117_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 1 v) = true := by decide +kernel
theorem col117_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 2 v) = true := by decide +kernel
theorem s117_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 0 = true := by decide +kernel
theorem s117_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 1 = true := by decide +kernel
theorem s117_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 2 = true := by decide +kernel
theorem k117_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k117_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k117_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s117_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k117_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k117_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k117_3_3_26 k h.1 (by omega)
theorem s117_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 4 = true := by decide +kernel
theorem s117_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 5 = true := by decide +kernel
theorem k117_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k117_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k117_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k117_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k117_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k117_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k117_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k117_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k117_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k117_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k117_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s117_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k117_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k117_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k117_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k117_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k117_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k117_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k117_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k117_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k117_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k117_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k117_3_6_130 k h.1 (by omega)
theorem s117_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 3 7 = true := by decide +kernel
theorem s117_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 0 = true := by decide +kernel
theorem s117_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 1 = true := by decide +kernel
theorem s117_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 2 = true := by decide +kernel
theorem s117_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 3 = true := by decide +kernel
theorem s117_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 4 = true := by decide +kernel
theorem s117_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 5 = true := by decide +kernel
theorem k117_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k117_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k117_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k117_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k117_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k117_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k117_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s117_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k117_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k117_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k117_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k117_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k117_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k117_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k117_4_6_126 k h.1 (by omega)
theorem s117_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 4 7 = true := by decide +kernel
theorem s117_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 0 = true := by decide +kernel
theorem s117_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 1 = true := by decide +kernel
theorem s117_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 2 = true := by decide +kernel
theorem s117_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 3 = true := by decide +kernel
theorem s117_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 4 = true := by decide +kernel
theorem s117_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 5 = true := by decide +kernel
theorem k117_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k117_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k117_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k117_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k117_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k117_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k117_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s117_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k117_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k117_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k117_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k117_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k117_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k117_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 117) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (117 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k117_5_6_126 k h.1 (by omega)
theorem s117_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 5 7 = true := by decide +kernel
theorem s117_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 0 = true := by decide +kernel
theorem s117_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 1 = true := by decide +kernel
theorem s117_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 2 = true := by decide +kernel
theorem s117_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 3 = true := by decide +kernel
theorem s117_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 4 = true := by decide +kernel
theorem s117_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 5 = true := by decide +kernel
theorem s117_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 6 = true := by decide +kernel
theorem k117_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k117_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k117_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k117_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k117_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s117_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k117_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k117_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k117_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k117_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 117) ((InDA1.TCasaD 6 6 7).getD (117 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k117_6_7_12 k h.1 (by omega)
theorem col117_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 7 v) = true := by decide +kernel
theorem col117 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 117) 117 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col117_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col117_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col117_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s117_3_0
    · exact s117_3_1
    · exact s117_3_2
    · exact s117_3_3
    · exact s117_3_4
    · exact s117_3_5
    · exact s117_3_6
    · exact s117_3_7
  · fin_cases v
    · exact s117_4_0
    · exact s117_4_1
    · exact s117_4_2
    · exact s117_4_3
    · exact s117_4_4
    · exact s117_4_5
    · exact s117_4_6
    · exact s117_4_7
  · fin_cases v
    · exact s117_5_0
    · exact s117_5_1
    · exact s117_5_2
    · exact s117_5_3
    · exact s117_5_4
    · exact s117_5_5
    · exact s117_5_6
    · exact s117_5_7
  · fin_cases v
    · exact s117_6_0
    · exact s117_6_1
    · exact s117_6_2
    · exact s117_6_3
    · exact s117_6_4
    · exact s117_6_5
    · exact s117_6_6
    · exact s117_6_7
  · exact List.all_eq_true.mp col117_7 v (List.mem_finRange v)
theorem col118_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 0 v) = true := by decide +kernel
theorem col118_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 1 v) = true := by decide +kernel
theorem col118_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 2 v) = true := by decide +kernel
theorem s118_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 0 = true := by decide +kernel
theorem s118_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 1 = true := by decide +kernel
theorem s118_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 2 = true := by decide +kernel
theorem k118_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k118_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k118_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s118_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k118_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k118_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k118_3_3_26 k h.1 (by omega)
theorem s118_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 4 = true := by decide +kernel
theorem s118_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 5 = true := by decide +kernel
theorem k118_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k118_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k118_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k118_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k118_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k118_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k118_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k118_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k118_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k118_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k118_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s118_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k118_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k118_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k118_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k118_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k118_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k118_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k118_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k118_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k118_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k118_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k118_3_6_130 k h.1 (by omega)
theorem s118_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 3 7 = true := by decide +kernel
theorem s118_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 0 = true := by decide +kernel
theorem s118_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 1 = true := by decide +kernel
theorem s118_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 2 = true := by decide +kernel
theorem s118_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 3 = true := by decide +kernel
theorem s118_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 4 = true := by decide +kernel
theorem s118_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 5 = true := by decide +kernel
theorem k118_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k118_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k118_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k118_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k118_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k118_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k118_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s118_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k118_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k118_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k118_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k118_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k118_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k118_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k118_4_6_126 k h.1 (by omega)
theorem s118_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 4 7 = true := by decide +kernel
theorem s118_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 0 = true := by decide +kernel
theorem s118_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 1 = true := by decide +kernel
theorem s118_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 2 = true := by decide +kernel
theorem s118_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 3 = true := by decide +kernel
theorem s118_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 4 = true := by decide +kernel
theorem s118_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 5 = true := by decide +kernel
theorem k118_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k118_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k118_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k118_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k118_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k118_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k118_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s118_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k118_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k118_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k118_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k118_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k118_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k118_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 118) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (118 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k118_5_6_126 k h.1 (by omega)
theorem s118_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 5 7 = true := by decide +kernel
theorem s118_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 0 = true := by decide +kernel
theorem s118_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 1 = true := by decide +kernel
theorem s118_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 2 = true := by decide +kernel
theorem s118_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 3 = true := by decide +kernel
theorem s118_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 4 = true := by decide +kernel
theorem s118_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 5 = true := by decide +kernel
theorem s118_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 6 = true := by decide +kernel
theorem k118_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k118_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k118_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k118_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k118_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s118_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k118_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k118_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k118_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k118_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 118) ((InDA1.TCasaD 6 6 7).getD (118 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k118_6_7_12 k h.1 (by omega)
theorem col118_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 7 v) = true := by decide +kernel
theorem col118 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 118) 118 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col118_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col118_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col118_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s118_3_0
    · exact s118_3_1
    · exact s118_3_2
    · exact s118_3_3
    · exact s118_3_4
    · exact s118_3_5
    · exact s118_3_6
    · exact s118_3_7
  · fin_cases v
    · exact s118_4_0
    · exact s118_4_1
    · exact s118_4_2
    · exact s118_4_3
    · exact s118_4_4
    · exact s118_4_5
    · exact s118_4_6
    · exact s118_4_7
  · fin_cases v
    · exact s118_5_0
    · exact s118_5_1
    · exact s118_5_2
    · exact s118_5_3
    · exact s118_5_4
    · exact s118_5_5
    · exact s118_5_6
    · exact s118_5_7
  · fin_cases v
    · exact s118_6_0
    · exact s118_6_1
    · exact s118_6_2
    · exact s118_6_3
    · exact s118_6_4
    · exact s118_6_5
    · exact s118_6_6
    · exact s118_6_7
  · exact List.all_eq_true.mp col118_7 v (List.mem_finRange v)
theorem col119_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 0 v) = true := by decide +kernel
theorem col119_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 1 v) = true := by decide +kernel
theorem col119_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 2 v) = true := by decide +kernel
theorem s119_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 0 = true := by decide +kernel
theorem s119_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 1 = true := by decide +kernel
theorem s119_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 2 = true := by decide +kernel
theorem k119_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k119_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k119_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s119_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k119_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k119_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k119_3_3_26 k h.1 (by omega)
theorem s119_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 4 = true := by decide +kernel
theorem s119_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 5 = true := by decide +kernel
theorem k119_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k119_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k119_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k119_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k119_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k119_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k119_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k119_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k119_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k119_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k119_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s119_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k119_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k119_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k119_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k119_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k119_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k119_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k119_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k119_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k119_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k119_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k119_3_6_130 k h.1 (by omega)
theorem s119_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 3 7 = true := by decide +kernel
theorem s119_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 0 = true := by decide +kernel
theorem s119_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 1 = true := by decide +kernel
theorem s119_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 2 = true := by decide +kernel
theorem s119_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 3 = true := by decide +kernel
theorem s119_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 4 = true := by decide +kernel
theorem s119_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 5 = true := by decide +kernel
theorem k119_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k119_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k119_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k119_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k119_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k119_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k119_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s119_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k119_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k119_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k119_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k119_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k119_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k119_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k119_4_6_126 k h.1 (by omega)
theorem s119_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 4 7 = true := by decide +kernel
theorem s119_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 0 = true := by decide +kernel
theorem s119_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 1 = true := by decide +kernel
theorem s119_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 2 = true := by decide +kernel
theorem s119_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 3 = true := by decide +kernel
theorem s119_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 4 = true := by decide +kernel
theorem s119_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 5 = true := by decide +kernel
theorem k119_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k119_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k119_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k119_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k119_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k119_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k119_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s119_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k119_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k119_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k119_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k119_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k119_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k119_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 119) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (119 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k119_5_6_126 k h.1 (by omega)
theorem s119_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 5 7 = true := by decide +kernel
theorem s119_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 0 = true := by decide +kernel
theorem s119_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 1 = true := by decide +kernel
theorem s119_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 2 = true := by decide +kernel
theorem s119_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 3 = true := by decide +kernel
theorem s119_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 4 = true := by decide +kernel
theorem s119_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 5 = true := by decide +kernel
theorem s119_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 6 = true := by decide +kernel
theorem k119_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k119_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k119_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k119_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k119_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s119_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k119_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k119_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k119_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k119_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 119) ((InDA1.TCasaD 6 6 7).getD (119 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k119_6_7_12 k h.1 (by omega)
theorem col119_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 7 v) = true := by decide +kernel
theorem col119 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 119) 119 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col119_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col119_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col119_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s119_3_0
    · exact s119_3_1
    · exact s119_3_2
    · exact s119_3_3
    · exact s119_3_4
    · exact s119_3_5
    · exact s119_3_6
    · exact s119_3_7
  · fin_cases v
    · exact s119_4_0
    · exact s119_4_1
    · exact s119_4_2
    · exact s119_4_3
    · exact s119_4_4
    · exact s119_4_5
    · exact s119_4_6
    · exact s119_4_7
  · fin_cases v
    · exact s119_5_0
    · exact s119_5_1
    · exact s119_5_2
    · exact s119_5_3
    · exact s119_5_4
    · exact s119_5_5
    · exact s119_5_6
    · exact s119_5_7
  · fin_cases v
    · exact s119_6_0
    · exact s119_6_1
    · exact s119_6_2
    · exact s119_6_3
    · exact s119_6_4
    · exact s119_6_5
    · exact s119_6_6
    · exact s119_6_7
  · exact List.all_eq_true.mp col119_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
