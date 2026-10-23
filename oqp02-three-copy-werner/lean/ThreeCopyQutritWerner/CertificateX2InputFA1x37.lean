module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [185, 190). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col185_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 0 v) = true := by decide +kernel
theorem col185_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 1 v) = true := by decide +kernel
theorem col185_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 2 v) = true := by decide +kernel
theorem s185_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 0 = true := by decide +kernel
theorem s185_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 1 = true := by decide +kernel
theorem s185_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 2 = true := by decide +kernel
theorem k185_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k185_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k185_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s185_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k185_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k185_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k185_3_3_26 k h.1 (by omega)
theorem s185_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 4 = true := by decide +kernel
theorem s185_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 5 = true := by decide +kernel
theorem k185_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k185_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k185_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k185_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k185_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k185_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k185_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k185_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k185_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k185_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k185_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s185_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k185_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k185_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k185_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k185_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k185_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k185_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k185_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k185_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k185_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k185_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k185_3_6_130 k h.1 (by omega)
theorem s185_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 3 7 = true := by decide +kernel
theorem s185_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 0 = true := by decide +kernel
theorem s185_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 1 = true := by decide +kernel
theorem s185_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 2 = true := by decide +kernel
theorem s185_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 3 = true := by decide +kernel
theorem s185_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 4 = true := by decide +kernel
theorem s185_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 5 = true := by decide +kernel
theorem k185_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k185_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k185_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k185_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k185_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k185_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k185_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s185_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k185_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k185_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k185_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k185_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k185_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k185_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k185_4_6_126 k h.1 (by omega)
theorem s185_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 4 7 = true := by decide +kernel
theorem s185_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 0 = true := by decide +kernel
theorem s185_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 1 = true := by decide +kernel
theorem s185_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 2 = true := by decide +kernel
theorem s185_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 3 = true := by decide +kernel
theorem s185_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 4 = true := by decide +kernel
theorem s185_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 5 = true := by decide +kernel
theorem k185_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k185_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k185_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k185_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k185_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k185_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k185_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s185_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k185_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k185_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k185_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k185_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k185_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k185_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 185) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (185 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k185_5_6_126 k h.1 (by omega)
theorem s185_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 5 7 = true := by decide +kernel
theorem s185_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 0 = true := by decide +kernel
theorem s185_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 1 = true := by decide +kernel
theorem s185_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 2 = true := by decide +kernel
theorem s185_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 3 = true := by decide +kernel
theorem s185_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 4 = true := by decide +kernel
theorem s185_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 5 = true := by decide +kernel
theorem s185_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 6 = true := by decide +kernel
theorem k185_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k185_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k185_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k185_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k185_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s185_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k185_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k185_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k185_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k185_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 185) ((InDA1.TCasaD 6 6 7).getD (185 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k185_6_7_12 k h.1 (by omega)
theorem col185_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 7 v) = true := by decide +kernel
theorem col185 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 185) 185 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col185_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col185_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col185_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s185_3_0
    · exact s185_3_1
    · exact s185_3_2
    · exact s185_3_3
    · exact s185_3_4
    · exact s185_3_5
    · exact s185_3_6
    · exact s185_3_7
  · fin_cases v
    · exact s185_4_0
    · exact s185_4_1
    · exact s185_4_2
    · exact s185_4_3
    · exact s185_4_4
    · exact s185_4_5
    · exact s185_4_6
    · exact s185_4_7
  · fin_cases v
    · exact s185_5_0
    · exact s185_5_1
    · exact s185_5_2
    · exact s185_5_3
    · exact s185_5_4
    · exact s185_5_5
    · exact s185_5_6
    · exact s185_5_7
  · fin_cases v
    · exact s185_6_0
    · exact s185_6_1
    · exact s185_6_2
    · exact s185_6_3
    · exact s185_6_4
    · exact s185_6_5
    · exact s185_6_6
    · exact s185_6_7
  · exact List.all_eq_true.mp col185_7 v (List.mem_finRange v)
theorem col186_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 0 v) = true := by decide +kernel
theorem col186_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 1 v) = true := by decide +kernel
theorem col186_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 2 v) = true := by decide +kernel
theorem s186_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 0 = true := by decide +kernel
theorem s186_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 1 = true := by decide +kernel
theorem s186_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 2 = true := by decide +kernel
theorem k186_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k186_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k186_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s186_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k186_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k186_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k186_3_3_26 k h.1 (by omega)
theorem s186_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 4 = true := by decide +kernel
theorem s186_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 5 = true := by decide +kernel
theorem k186_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k186_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k186_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k186_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k186_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k186_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k186_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k186_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k186_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k186_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k186_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s186_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k186_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k186_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k186_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k186_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k186_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k186_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k186_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k186_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k186_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k186_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k186_3_6_130 k h.1 (by omega)
theorem s186_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 3 7 = true := by decide +kernel
theorem s186_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 0 = true := by decide +kernel
theorem s186_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 1 = true := by decide +kernel
theorem s186_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 2 = true := by decide +kernel
theorem s186_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 3 = true := by decide +kernel
theorem s186_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 4 = true := by decide +kernel
theorem s186_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 5 = true := by decide +kernel
theorem k186_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k186_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k186_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k186_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k186_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k186_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k186_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s186_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k186_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k186_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k186_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k186_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k186_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k186_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k186_4_6_126 k h.1 (by omega)
theorem s186_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 4 7 = true := by decide +kernel
theorem s186_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 0 = true := by decide +kernel
theorem s186_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 1 = true := by decide +kernel
theorem s186_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 2 = true := by decide +kernel
theorem s186_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 3 = true := by decide +kernel
theorem s186_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 4 = true := by decide +kernel
theorem s186_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 5 = true := by decide +kernel
theorem k186_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k186_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k186_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k186_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k186_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k186_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k186_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s186_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k186_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k186_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k186_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k186_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k186_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k186_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 186) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (186 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k186_5_6_126 k h.1 (by omega)
theorem s186_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 5 7 = true := by decide +kernel
theorem s186_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 0 = true := by decide +kernel
theorem s186_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 1 = true := by decide +kernel
theorem s186_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 2 = true := by decide +kernel
theorem s186_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 3 = true := by decide +kernel
theorem s186_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 4 = true := by decide +kernel
theorem s186_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 5 = true := by decide +kernel
theorem s186_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 6 = true := by decide +kernel
theorem k186_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k186_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k186_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k186_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k186_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s186_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k186_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k186_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k186_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k186_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 186) ((InDA1.TCasaD 6 6 7).getD (186 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k186_6_7_12 k h.1 (by omega)
theorem col186_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 7 v) = true := by decide +kernel
theorem col186 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 186) 186 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col186_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col186_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col186_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s186_3_0
    · exact s186_3_1
    · exact s186_3_2
    · exact s186_3_3
    · exact s186_3_4
    · exact s186_3_5
    · exact s186_3_6
    · exact s186_3_7
  · fin_cases v
    · exact s186_4_0
    · exact s186_4_1
    · exact s186_4_2
    · exact s186_4_3
    · exact s186_4_4
    · exact s186_4_5
    · exact s186_4_6
    · exact s186_4_7
  · fin_cases v
    · exact s186_5_0
    · exact s186_5_1
    · exact s186_5_2
    · exact s186_5_3
    · exact s186_5_4
    · exact s186_5_5
    · exact s186_5_6
    · exact s186_5_7
  · fin_cases v
    · exact s186_6_0
    · exact s186_6_1
    · exact s186_6_2
    · exact s186_6_3
    · exact s186_6_4
    · exact s186_6_5
    · exact s186_6_6
    · exact s186_6_7
  · exact List.all_eq_true.mp col186_7 v (List.mem_finRange v)
theorem col187_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 0 v) = true := by decide +kernel
theorem col187_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 1 v) = true := by decide +kernel
theorem col187_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 2 v) = true := by decide +kernel
theorem s187_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 0 = true := by decide +kernel
theorem s187_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 1 = true := by decide +kernel
theorem s187_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 2 = true := by decide +kernel
theorem k187_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k187_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k187_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s187_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k187_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k187_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k187_3_3_26 k h.1 (by omega)
theorem s187_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 4 = true := by decide +kernel
theorem s187_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 5 = true := by decide +kernel
theorem k187_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k187_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k187_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k187_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k187_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k187_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k187_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k187_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k187_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k187_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k187_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s187_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k187_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k187_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k187_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k187_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k187_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k187_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k187_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k187_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k187_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k187_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k187_3_6_130 k h.1 (by omega)
theorem s187_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 3 7 = true := by decide +kernel
theorem s187_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 0 = true := by decide +kernel
theorem s187_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 1 = true := by decide +kernel
theorem s187_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 2 = true := by decide +kernel
theorem s187_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 3 = true := by decide +kernel
theorem s187_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 4 = true := by decide +kernel
theorem s187_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 5 = true := by decide +kernel
theorem k187_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k187_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k187_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k187_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k187_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k187_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k187_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s187_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k187_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k187_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k187_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k187_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k187_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k187_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k187_4_6_126 k h.1 (by omega)
theorem s187_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 4 7 = true := by decide +kernel
theorem s187_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 0 = true := by decide +kernel
theorem s187_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 1 = true := by decide +kernel
theorem s187_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 2 = true := by decide +kernel
theorem s187_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 3 = true := by decide +kernel
theorem s187_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 4 = true := by decide +kernel
theorem s187_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 5 = true := by decide +kernel
theorem k187_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k187_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k187_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k187_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k187_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k187_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k187_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s187_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k187_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k187_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k187_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k187_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k187_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k187_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 187) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (187 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k187_5_6_126 k h.1 (by omega)
theorem s187_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 5 7 = true := by decide +kernel
theorem s187_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 0 = true := by decide +kernel
theorem s187_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 1 = true := by decide +kernel
theorem s187_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 2 = true := by decide +kernel
theorem s187_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 3 = true := by decide +kernel
theorem s187_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 4 = true := by decide +kernel
theorem s187_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 5 = true := by decide +kernel
theorem s187_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 6 = true := by decide +kernel
theorem k187_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k187_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k187_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k187_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k187_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s187_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k187_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k187_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k187_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k187_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 187) ((InDA1.TCasaD 6 6 7).getD (187 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k187_6_7_12 k h.1 (by omega)
theorem col187_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 7 v) = true := by decide +kernel
theorem col187 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 187) 187 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col187_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col187_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col187_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s187_3_0
    · exact s187_3_1
    · exact s187_3_2
    · exact s187_3_3
    · exact s187_3_4
    · exact s187_3_5
    · exact s187_3_6
    · exact s187_3_7
  · fin_cases v
    · exact s187_4_0
    · exact s187_4_1
    · exact s187_4_2
    · exact s187_4_3
    · exact s187_4_4
    · exact s187_4_5
    · exact s187_4_6
    · exact s187_4_7
  · fin_cases v
    · exact s187_5_0
    · exact s187_5_1
    · exact s187_5_2
    · exact s187_5_3
    · exact s187_5_4
    · exact s187_5_5
    · exact s187_5_6
    · exact s187_5_7
  · fin_cases v
    · exact s187_6_0
    · exact s187_6_1
    · exact s187_6_2
    · exact s187_6_3
    · exact s187_6_4
    · exact s187_6_5
    · exact s187_6_6
    · exact s187_6_7
  · exact List.all_eq_true.mp col187_7 v (List.mem_finRange v)
theorem col188_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 0 v) = true := by decide +kernel
theorem col188_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 1 v) = true := by decide +kernel
theorem col188_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 2 v) = true := by decide +kernel
theorem s188_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 0 = true := by decide +kernel
theorem s188_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 1 = true := by decide +kernel
theorem s188_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 2 = true := by decide +kernel
theorem k188_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k188_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k188_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s188_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k188_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k188_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k188_3_3_26 k h.1 (by omega)
theorem s188_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 4 = true := by decide +kernel
theorem s188_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 5 = true := by decide +kernel
theorem k188_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k188_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k188_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k188_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k188_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k188_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k188_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k188_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k188_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k188_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k188_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s188_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k188_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k188_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k188_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k188_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k188_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k188_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k188_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k188_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k188_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k188_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k188_3_6_130 k h.1 (by omega)
theorem s188_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 3 7 = true := by decide +kernel
theorem s188_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 0 = true := by decide +kernel
theorem s188_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 1 = true := by decide +kernel
theorem s188_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 2 = true := by decide +kernel
theorem s188_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 3 = true := by decide +kernel
theorem s188_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 4 = true := by decide +kernel
theorem s188_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 5 = true := by decide +kernel
theorem k188_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k188_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k188_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k188_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k188_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k188_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k188_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s188_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k188_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k188_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k188_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k188_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k188_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k188_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k188_4_6_126 k h.1 (by omega)
theorem s188_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 4 7 = true := by decide +kernel
theorem s188_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 0 = true := by decide +kernel
theorem s188_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 1 = true := by decide +kernel
theorem s188_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 2 = true := by decide +kernel
theorem s188_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 3 = true := by decide +kernel
theorem s188_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 4 = true := by decide +kernel
theorem s188_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 5 = true := by decide +kernel
theorem k188_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k188_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k188_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k188_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k188_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k188_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k188_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s188_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k188_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k188_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k188_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k188_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k188_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k188_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 188) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (188 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k188_5_6_126 k h.1 (by omega)
theorem s188_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 5 7 = true := by decide +kernel
theorem s188_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 0 = true := by decide +kernel
theorem s188_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 1 = true := by decide +kernel
theorem s188_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 2 = true := by decide +kernel
theorem s188_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 3 = true := by decide +kernel
theorem s188_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 4 = true := by decide +kernel
theorem s188_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 5 = true := by decide +kernel
theorem s188_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 6 = true := by decide +kernel
theorem k188_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k188_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k188_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k188_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k188_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s188_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k188_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k188_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k188_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k188_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 188) ((InDA1.TCasaD 6 6 7).getD (188 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k188_6_7_12 k h.1 (by omega)
theorem col188_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 7 v) = true := by decide +kernel
theorem col188 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 188) 188 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col188_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col188_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col188_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s188_3_0
    · exact s188_3_1
    · exact s188_3_2
    · exact s188_3_3
    · exact s188_3_4
    · exact s188_3_5
    · exact s188_3_6
    · exact s188_3_7
  · fin_cases v
    · exact s188_4_0
    · exact s188_4_1
    · exact s188_4_2
    · exact s188_4_3
    · exact s188_4_4
    · exact s188_4_5
    · exact s188_4_6
    · exact s188_4_7
  · fin_cases v
    · exact s188_5_0
    · exact s188_5_1
    · exact s188_5_2
    · exact s188_5_3
    · exact s188_5_4
    · exact s188_5_5
    · exact s188_5_6
    · exact s188_5_7
  · fin_cases v
    · exact s188_6_0
    · exact s188_6_1
    · exact s188_6_2
    · exact s188_6_3
    · exact s188_6_4
    · exact s188_6_5
    · exact s188_6_6
    · exact s188_6_7
  · exact List.all_eq_true.mp col188_7 v (List.mem_finRange v)
theorem col189_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 0 v) = true := by decide +kernel
theorem col189_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 1 v) = true := by decide +kernel
theorem col189_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 2 v) = true := by decide +kernel
theorem s189_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 0 = true := by decide +kernel
theorem s189_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 1 = true := by decide +kernel
theorem s189_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 2 = true := by decide +kernel
theorem k189_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k189_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k189_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s189_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k189_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k189_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k189_3_3_26 k h.1 (by omega)
theorem s189_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 4 = true := by decide +kernel
theorem s189_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 5 = true := by decide +kernel
theorem k189_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k189_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k189_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k189_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k189_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k189_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k189_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k189_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k189_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k189_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k189_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s189_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k189_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k189_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k189_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k189_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k189_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k189_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k189_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k189_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k189_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k189_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k189_3_6_130 k h.1 (by omega)
theorem s189_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 3 7 = true := by decide +kernel
theorem s189_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 0 = true := by decide +kernel
theorem s189_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 1 = true := by decide +kernel
theorem s189_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 2 = true := by decide +kernel
theorem s189_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 3 = true := by decide +kernel
theorem s189_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 4 = true := by decide +kernel
theorem s189_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 5 = true := by decide +kernel
theorem k189_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k189_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k189_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k189_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k189_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k189_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k189_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s189_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k189_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k189_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k189_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k189_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k189_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k189_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k189_4_6_126 k h.1 (by omega)
theorem s189_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 4 7 = true := by decide +kernel
theorem s189_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 0 = true := by decide +kernel
theorem s189_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 1 = true := by decide +kernel
theorem s189_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 2 = true := by decide +kernel
theorem s189_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 3 = true := by decide +kernel
theorem s189_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 4 = true := by decide +kernel
theorem s189_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 5 = true := by decide +kernel
theorem k189_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k189_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k189_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k189_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k189_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k189_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k189_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s189_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k189_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k189_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k189_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k189_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k189_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k189_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 189) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (189 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k189_5_6_126 k h.1 (by omega)
theorem s189_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 5 7 = true := by decide +kernel
theorem s189_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 0 = true := by decide +kernel
theorem s189_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 1 = true := by decide +kernel
theorem s189_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 2 = true := by decide +kernel
theorem s189_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 3 = true := by decide +kernel
theorem s189_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 4 = true := by decide +kernel
theorem s189_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 5 = true := by decide +kernel
theorem s189_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 6 = true := by decide +kernel
theorem k189_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k189_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k189_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k189_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k189_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s189_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k189_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k189_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k189_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k189_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 189) ((InDA1.TCasaD 6 6 7).getD (189 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k189_6_7_12 k h.1 (by omega)
theorem col189_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 7 v) = true := by decide +kernel
theorem col189 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 189) 189 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col189_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col189_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col189_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s189_3_0
    · exact s189_3_1
    · exact s189_3_2
    · exact s189_3_3
    · exact s189_3_4
    · exact s189_3_5
    · exact s189_3_6
    · exact s189_3_7
  · fin_cases v
    · exact s189_4_0
    · exact s189_4_1
    · exact s189_4_2
    · exact s189_4_3
    · exact s189_4_4
    · exact s189_4_5
    · exact s189_4_6
    · exact s189_4_7
  · fin_cases v
    · exact s189_5_0
    · exact s189_5_1
    · exact s189_5_2
    · exact s189_5_3
    · exact s189_5_4
    · exact s189_5_5
    · exact s189_5_6
    · exact s189_5_7
  · fin_cases v
    · exact s189_6_0
    · exact s189_6_1
    · exact s189_6_2
    · exact s189_6_3
    · exact s189_6_4
    · exact s189_6_5
    · exact s189_6_6
    · exact s189_6_7
  · exact List.all_eq_true.mp col189_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
