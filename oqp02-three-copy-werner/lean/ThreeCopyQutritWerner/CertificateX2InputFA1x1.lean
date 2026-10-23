module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [5, 10). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col5_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 0 v) = true := by decide +kernel
theorem col5_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 1 v) = true := by decide +kernel
theorem col5_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 2 v) = true := by decide +kernel
theorem s5_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 0 = true := by decide +kernel
theorem s5_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 1 = true := by decide +kernel
theorem s5_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 2 = true := by decide +kernel
theorem s5_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 3 = true := by decide +kernel
theorem s5_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 4 = true := by decide +kernel
theorem s5_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 5 = true := by decide +kernel
theorem k5_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k5_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k5_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k5_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k5_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k5_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k5_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k5_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k5_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k5_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k5_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s5_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k5_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k5_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k5_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k5_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k5_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k5_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k5_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k5_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k5_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k5_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 3 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k5_3_6_130 k h.1 (by omega)
theorem s5_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 3 7 = true := by decide +kernel
theorem s5_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 0 = true := by decide +kernel
theorem s5_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 1 = true := by decide +kernel
theorem s5_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 2 = true := by decide +kernel
theorem s5_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 3 = true := by decide +kernel
theorem s5_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 4 = true := by decide +kernel
theorem s5_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 5 = true := by decide +kernel
theorem k5_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k5_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k5_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k5_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k5_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k5_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k5_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s5_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k5_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k5_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k5_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k5_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k5_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k5_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 4 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k5_4_6_126 k h.1 (by omega)
theorem s5_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 4 7 = true := by decide +kernel
theorem s5_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 0 = true := by decide +kernel
theorem s5_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 1 = true := by decide +kernel
theorem s5_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 2 = true := by decide +kernel
theorem s5_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 3 = true := by decide +kernel
theorem s5_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 4 = true := by decide +kernel
theorem s5_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 5 = true := by decide +kernel
theorem k5_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k5_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k5_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k5_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k5_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k5_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k5_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s5_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k5_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k5_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k5_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k5_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k5_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k5_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 5 6).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k5_5_6_126 k h.1 (by omega)
theorem s5_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 5 7 = true := by decide +kernel
theorem s5_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 0 = true := by decide +kernel
theorem s5_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 1 = true := by decide +kernel
theorem s5_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 2 = true := by decide +kernel
theorem s5_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 3 = true := by decide +kernel
theorem s5_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 4 = true := by decide +kernel
theorem s5_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 5 = true := by decide +kernel
theorem s5_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 6 = true := by decide +kernel
theorem k5_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k5_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k5_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k5_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k5_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s5_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k5_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k5_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k5_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k5_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 5) ((InDA1.TCasaD 3 6 7).getD (5 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k5_6_7_12 k h.1 (by omega)
theorem col5_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 7 v) = true := by decide +kernel
theorem col5 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 5) 5 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col5_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col5_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col5_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s5_3_0
    · exact s5_3_1
    · exact s5_3_2
    · exact s5_3_3
    · exact s5_3_4
    · exact s5_3_5
    · exact s5_3_6
    · exact s5_3_7
  · fin_cases v
    · exact s5_4_0
    · exact s5_4_1
    · exact s5_4_2
    · exact s5_4_3
    · exact s5_4_4
    · exact s5_4_5
    · exact s5_4_6
    · exact s5_4_7
  · fin_cases v
    · exact s5_5_0
    · exact s5_5_1
    · exact s5_5_2
    · exact s5_5_3
    · exact s5_5_4
    · exact s5_5_5
    · exact s5_5_6
    · exact s5_5_7
  · fin_cases v
    · exact s5_6_0
    · exact s5_6_1
    · exact s5_6_2
    · exact s5_6_3
    · exact s5_6_4
    · exact s5_6_5
    · exact s5_6_6
    · exact s5_6_7
  · exact List.all_eq_true.mp col5_7 v (List.mem_finRange v)
theorem col6_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 0 v) = true := by decide +kernel
theorem col6_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 1 v) = true := by decide +kernel
theorem col6_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 2 v) = true := by decide +kernel
theorem s6_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 0 = true := by decide +kernel
theorem s6_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 1 = true := by decide +kernel
theorem s6_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 2 = true := by decide +kernel
theorem s6_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 3 = true := by decide +kernel
theorem s6_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 4 = true := by decide +kernel
theorem s6_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 5 = true := by decide +kernel
theorem k6_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k6_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k6_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k6_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k6_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k6_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k6_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k6_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k6_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k6_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k6_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s6_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k6_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k6_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k6_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k6_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k6_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k6_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k6_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k6_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k6_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k6_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 3 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k6_3_6_130 k h.1 (by omega)
theorem s6_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 3 7 = true := by decide +kernel
theorem s6_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 0 = true := by decide +kernel
theorem s6_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 1 = true := by decide +kernel
theorem s6_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 2 = true := by decide +kernel
theorem s6_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 3 = true := by decide +kernel
theorem s6_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 4 = true := by decide +kernel
theorem s6_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 5 = true := by decide +kernel
theorem k6_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k6_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k6_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k6_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k6_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k6_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k6_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s6_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k6_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k6_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k6_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k6_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k6_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k6_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 4 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k6_4_6_126 k h.1 (by omega)
theorem s6_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 4 7 = true := by decide +kernel
theorem s6_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 0 = true := by decide +kernel
theorem s6_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 1 = true := by decide +kernel
theorem s6_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 2 = true := by decide +kernel
theorem s6_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 3 = true := by decide +kernel
theorem s6_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 4 = true := by decide +kernel
theorem s6_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 5 = true := by decide +kernel
theorem k6_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k6_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k6_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k6_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k6_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k6_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k6_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s6_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k6_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k6_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k6_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k6_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k6_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k6_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 5 6).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k6_5_6_126 k h.1 (by omega)
theorem s6_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 5 7 = true := by decide +kernel
theorem s6_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 0 = true := by decide +kernel
theorem s6_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 1 = true := by decide +kernel
theorem s6_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 2 = true := by decide +kernel
theorem s6_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 3 = true := by decide +kernel
theorem s6_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 4 = true := by decide +kernel
theorem s6_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 5 = true := by decide +kernel
theorem s6_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 6 = true := by decide +kernel
theorem k6_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k6_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k6_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k6_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k6_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s6_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k6_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k6_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k6_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k6_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 6) ((InDA1.TCasaD 3 6 7).getD (6 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k6_6_7_12 k h.1 (by omega)
theorem col6_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 7 v) = true := by decide +kernel
theorem col6 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 6) 6 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col6_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col6_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col6_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s6_3_0
    · exact s6_3_1
    · exact s6_3_2
    · exact s6_3_3
    · exact s6_3_4
    · exact s6_3_5
    · exact s6_3_6
    · exact s6_3_7
  · fin_cases v
    · exact s6_4_0
    · exact s6_4_1
    · exact s6_4_2
    · exact s6_4_3
    · exact s6_4_4
    · exact s6_4_5
    · exact s6_4_6
    · exact s6_4_7
  · fin_cases v
    · exact s6_5_0
    · exact s6_5_1
    · exact s6_5_2
    · exact s6_5_3
    · exact s6_5_4
    · exact s6_5_5
    · exact s6_5_6
    · exact s6_5_7
  · fin_cases v
    · exact s6_6_0
    · exact s6_6_1
    · exact s6_6_2
    · exact s6_6_3
    · exact s6_6_4
    · exact s6_6_5
    · exact s6_6_6
    · exact s6_6_7
  · exact List.all_eq_true.mp col6_7 v (List.mem_finRange v)
theorem col7_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 0 v) = true := by decide +kernel
theorem col7_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 1 v) = true := by decide +kernel
theorem col7_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 2 v) = true := by decide +kernel
theorem s7_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 0 = true := by decide +kernel
theorem s7_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 1 = true := by decide +kernel
theorem s7_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 2 = true := by decide +kernel
theorem s7_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 3 = true := by decide +kernel
theorem s7_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 4 = true := by decide +kernel
theorem s7_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 5 = true := by decide +kernel
theorem k7_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k7_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k7_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k7_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k7_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k7_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k7_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k7_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k7_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k7_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k7_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s7_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k7_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k7_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k7_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k7_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k7_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k7_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k7_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k7_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k7_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k7_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 3 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k7_3_6_130 k h.1 (by omega)
theorem s7_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 3 7 = true := by decide +kernel
theorem s7_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 0 = true := by decide +kernel
theorem s7_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 1 = true := by decide +kernel
theorem s7_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 2 = true := by decide +kernel
theorem s7_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 3 = true := by decide +kernel
theorem s7_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 4 = true := by decide +kernel
theorem s7_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 5 = true := by decide +kernel
theorem k7_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k7_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k7_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k7_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k7_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k7_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k7_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s7_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k7_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k7_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k7_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k7_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k7_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k7_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 4 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k7_4_6_126 k h.1 (by omega)
theorem s7_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 4 7 = true := by decide +kernel
theorem s7_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 0 = true := by decide +kernel
theorem s7_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 1 = true := by decide +kernel
theorem s7_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 2 = true := by decide +kernel
theorem s7_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 3 = true := by decide +kernel
theorem s7_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 4 = true := by decide +kernel
theorem s7_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 5 = true := by decide +kernel
theorem k7_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k7_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k7_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k7_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k7_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k7_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k7_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s7_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k7_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k7_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k7_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k7_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k7_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k7_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 5 6).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k7_5_6_126 k h.1 (by omega)
theorem s7_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 5 7 = true := by decide +kernel
theorem s7_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 0 = true := by decide +kernel
theorem s7_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 1 = true := by decide +kernel
theorem s7_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 2 = true := by decide +kernel
theorem s7_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 3 = true := by decide +kernel
theorem s7_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 4 = true := by decide +kernel
theorem s7_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 5 = true := by decide +kernel
theorem s7_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 6 = true := by decide +kernel
theorem k7_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k7_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k7_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k7_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k7_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s7_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k7_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k7_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k7_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k7_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 7) ((InDA1.TCasaD 3 6 7).getD (7 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k7_6_7_12 k h.1 (by omega)
theorem col7_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 7 v) = true := by decide +kernel
theorem col7 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 7) 7 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col7_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col7_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col7_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s7_3_0
    · exact s7_3_1
    · exact s7_3_2
    · exact s7_3_3
    · exact s7_3_4
    · exact s7_3_5
    · exact s7_3_6
    · exact s7_3_7
  · fin_cases v
    · exact s7_4_0
    · exact s7_4_1
    · exact s7_4_2
    · exact s7_4_3
    · exact s7_4_4
    · exact s7_4_5
    · exact s7_4_6
    · exact s7_4_7
  · fin_cases v
    · exact s7_5_0
    · exact s7_5_1
    · exact s7_5_2
    · exact s7_5_3
    · exact s7_5_4
    · exact s7_5_5
    · exact s7_5_6
    · exact s7_5_7
  · fin_cases v
    · exact s7_6_0
    · exact s7_6_1
    · exact s7_6_2
    · exact s7_6_3
    · exact s7_6_4
    · exact s7_6_5
    · exact s7_6_6
    · exact s7_6_7
  · exact List.all_eq_true.mp col7_7 v (List.mem_finRange v)
theorem col8_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 0 v) = true := by decide +kernel
theorem col8_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 1 v) = true := by decide +kernel
theorem col8_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 2 v) = true := by decide +kernel
theorem s8_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 0 = true := by decide +kernel
theorem s8_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 1 = true := by decide +kernel
theorem s8_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 2 = true := by decide +kernel
theorem s8_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 3 = true := by decide +kernel
theorem s8_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 4 = true := by decide +kernel
theorem s8_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 5 = true := by decide +kernel
theorem k8_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k8_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k8_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k8_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k8_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k8_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k8_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k8_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k8_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k8_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k8_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s8_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k8_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k8_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k8_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k8_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k8_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k8_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k8_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k8_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k8_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k8_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 3 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k8_3_6_130 k h.1 (by omega)
theorem s8_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 3 7 = true := by decide +kernel
theorem s8_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 0 = true := by decide +kernel
theorem s8_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 1 = true := by decide +kernel
theorem s8_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 2 = true := by decide +kernel
theorem s8_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 3 = true := by decide +kernel
theorem s8_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 4 = true := by decide +kernel
theorem s8_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 5 = true := by decide +kernel
theorem k8_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k8_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k8_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k8_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k8_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k8_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k8_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s8_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k8_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k8_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k8_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k8_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k8_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k8_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 4 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k8_4_6_126 k h.1 (by omega)
theorem s8_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 4 7 = true := by decide +kernel
theorem s8_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 0 = true := by decide +kernel
theorem s8_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 1 = true := by decide +kernel
theorem s8_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 2 = true := by decide +kernel
theorem s8_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 3 = true := by decide +kernel
theorem s8_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 4 = true := by decide +kernel
theorem s8_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 5 = true := by decide +kernel
theorem k8_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k8_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k8_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k8_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k8_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k8_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k8_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s8_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k8_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k8_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k8_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k8_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k8_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k8_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 5 6).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k8_5_6_126 k h.1 (by omega)
theorem s8_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 5 7 = true := by decide +kernel
theorem s8_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 0 = true := by decide +kernel
theorem s8_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 1 = true := by decide +kernel
theorem s8_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 2 = true := by decide +kernel
theorem s8_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 3 = true := by decide +kernel
theorem s8_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 4 = true := by decide +kernel
theorem s8_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 5 = true := by decide +kernel
theorem s8_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 6 = true := by decide +kernel
theorem k8_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k8_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k8_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k8_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k8_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s8_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k8_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k8_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k8_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k8_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 8) ((InDA1.TCasaD 3 6 7).getD (8 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k8_6_7_12 k h.1 (by omega)
theorem col8_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 7 v) = true := by decide +kernel
theorem col8 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 8) 8 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col8_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col8_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col8_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s8_3_0
    · exact s8_3_1
    · exact s8_3_2
    · exact s8_3_3
    · exact s8_3_4
    · exact s8_3_5
    · exact s8_3_6
    · exact s8_3_7
  · fin_cases v
    · exact s8_4_0
    · exact s8_4_1
    · exact s8_4_2
    · exact s8_4_3
    · exact s8_4_4
    · exact s8_4_5
    · exact s8_4_6
    · exact s8_4_7
  · fin_cases v
    · exact s8_5_0
    · exact s8_5_1
    · exact s8_5_2
    · exact s8_5_3
    · exact s8_5_4
    · exact s8_5_5
    · exact s8_5_6
    · exact s8_5_7
  · fin_cases v
    · exact s8_6_0
    · exact s8_6_1
    · exact s8_6_2
    · exact s8_6_3
    · exact s8_6_4
    · exact s8_6_5
    · exact s8_6_6
    · exact s8_6_7
  · exact List.all_eq_true.mp col8_7 v (List.mem_finRange v)
theorem col9_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 0 v) = true := by decide +kernel
theorem col9_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 1 v) = true := by decide +kernel
theorem col9_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 2 v) = true := by decide +kernel
theorem s9_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 0 = true := by decide +kernel
theorem s9_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 1 = true := by decide +kernel
theorem s9_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 2 = true := by decide +kernel
theorem s9_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 3 = true := by decide +kernel
theorem s9_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 4 = true := by decide +kernel
theorem s9_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 5 = true := by decide +kernel
theorem k9_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k9_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k9_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k9_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k9_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k9_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k9_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k9_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k9_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k9_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k9_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s9_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k9_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k9_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k9_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k9_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k9_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k9_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k9_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k9_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k9_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k9_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 3 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k9_3_6_130 k h.1 (by omega)
theorem s9_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 3 7 = true := by decide +kernel
theorem s9_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 0 = true := by decide +kernel
theorem s9_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 1 = true := by decide +kernel
theorem s9_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 2 = true := by decide +kernel
theorem s9_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 3 = true := by decide +kernel
theorem s9_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 4 = true := by decide +kernel
theorem s9_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 5 = true := by decide +kernel
theorem k9_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k9_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k9_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k9_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k9_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k9_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k9_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s9_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k9_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k9_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k9_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k9_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k9_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k9_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 4 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k9_4_6_126 k h.1 (by omega)
theorem s9_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 4 7 = true := by decide +kernel
theorem s9_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 0 = true := by decide +kernel
theorem s9_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 1 = true := by decide +kernel
theorem s9_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 2 = true := by decide +kernel
theorem s9_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 3 = true := by decide +kernel
theorem s9_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 4 = true := by decide +kernel
theorem s9_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 5 = true := by decide +kernel
theorem k9_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k9_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k9_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k9_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k9_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k9_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k9_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s9_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k9_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k9_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k9_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k9_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k9_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k9_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 5 6).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k9_5_6_126 k h.1 (by omega)
theorem s9_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 5 7 = true := by decide +kernel
theorem s9_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 0 = true := by decide +kernel
theorem s9_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 1 = true := by decide +kernel
theorem s9_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 2 = true := by decide +kernel
theorem s9_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 3 = true := by decide +kernel
theorem s9_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 4 = true := by decide +kernel
theorem s9_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 5 = true := by decide +kernel
theorem s9_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 6 = true := by decide +kernel
theorem k9_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k9_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k9_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k9_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k9_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s9_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k9_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k9_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k9_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k9_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 9) ((InDA1.TCasaD 3 6 7).getD (9 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k9_6_7_12 k h.1 (by omega)
theorem col9_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 7 v) = true := by decide +kernel
theorem col9 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 9) 9 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col9_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col9_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col9_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s9_3_0
    · exact s9_3_1
    · exact s9_3_2
    · exact s9_3_3
    · exact s9_3_4
    · exact s9_3_5
    · exact s9_3_6
    · exact s9_3_7
  · fin_cases v
    · exact s9_4_0
    · exact s9_4_1
    · exact s9_4_2
    · exact s9_4_3
    · exact s9_4_4
    · exact s9_4_5
    · exact s9_4_6
    · exact s9_4_7
  · fin_cases v
    · exact s9_5_0
    · exact s9_5_1
    · exact s9_5_2
    · exact s9_5_3
    · exact s9_5_4
    · exact s9_5_5
    · exact s9_5_6
    · exact s9_5_7
  · fin_cases v
    · exact s9_6_0
    · exact s9_6_1
    · exact s9_6_2
    · exact s9_6_3
    · exact s9_6_4
    · exact s9_6_5
    · exact s9_6_6
    · exact s9_6_7
  · exact List.all_eq_true.mp col9_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
