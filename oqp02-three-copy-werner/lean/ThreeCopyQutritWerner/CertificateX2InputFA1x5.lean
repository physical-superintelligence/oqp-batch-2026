module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [25, 30). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col25_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 0 v) = true := by decide +kernel
theorem col25_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 1 v) = true := by decide +kernel
theorem col25_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 2 v) = true := by decide +kernel
theorem s25_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 0 = true := by decide +kernel
theorem s25_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 1 = true := by decide +kernel
theorem s25_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 2 = true := by decide +kernel
theorem s25_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 3 = true := by decide +kernel
theorem s25_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 4 = true := by decide +kernel
theorem s25_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 5 = true := by decide +kernel
theorem k25_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k25_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k25_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k25_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k25_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k25_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k25_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k25_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k25_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k25_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k25_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s25_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k25_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k25_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k25_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k25_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k25_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k25_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k25_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k25_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k25_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k25_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 3 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k25_3_6_130 k h.1 (by omega)
theorem s25_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 3 7 = true := by decide +kernel
theorem s25_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 0 = true := by decide +kernel
theorem s25_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 1 = true := by decide +kernel
theorem s25_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 2 = true := by decide +kernel
theorem s25_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 3 = true := by decide +kernel
theorem s25_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 4 = true := by decide +kernel
theorem s25_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 5 = true := by decide +kernel
theorem k25_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k25_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k25_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k25_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k25_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k25_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k25_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s25_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k25_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k25_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k25_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k25_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k25_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k25_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 4 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k25_4_6_126 k h.1 (by omega)
theorem s25_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 4 7 = true := by decide +kernel
theorem s25_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 0 = true := by decide +kernel
theorem s25_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 1 = true := by decide +kernel
theorem s25_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 2 = true := by decide +kernel
theorem s25_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 3 = true := by decide +kernel
theorem s25_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 4 = true := by decide +kernel
theorem s25_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 5 = true := by decide +kernel
theorem k25_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k25_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k25_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k25_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k25_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k25_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k25_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s25_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k25_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k25_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k25_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k25_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k25_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k25_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 5 6).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k25_5_6_126 k h.1 (by omega)
theorem s25_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 5 7 = true := by decide +kernel
theorem s25_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 0 = true := by decide +kernel
theorem s25_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 1 = true := by decide +kernel
theorem s25_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 2 = true := by decide +kernel
theorem s25_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 3 = true := by decide +kernel
theorem s25_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 4 = true := by decide +kernel
theorem s25_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 5 = true := by decide +kernel
theorem s25_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 6 = true := by decide +kernel
theorem k25_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k25_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k25_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k25_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k25_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s25_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k25_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k25_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k25_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k25_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 25) ((InDA1.TCasaD 3 6 7).getD (25 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k25_6_7_12 k h.1 (by omega)
theorem col25_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 7 v) = true := by decide +kernel
theorem col25 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 25) 25 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col25_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col25_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col25_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s25_3_0
    · exact s25_3_1
    · exact s25_3_2
    · exact s25_3_3
    · exact s25_3_4
    · exact s25_3_5
    · exact s25_3_6
    · exact s25_3_7
  · fin_cases v
    · exact s25_4_0
    · exact s25_4_1
    · exact s25_4_2
    · exact s25_4_3
    · exact s25_4_4
    · exact s25_4_5
    · exact s25_4_6
    · exact s25_4_7
  · fin_cases v
    · exact s25_5_0
    · exact s25_5_1
    · exact s25_5_2
    · exact s25_5_3
    · exact s25_5_4
    · exact s25_5_5
    · exact s25_5_6
    · exact s25_5_7
  · fin_cases v
    · exact s25_6_0
    · exact s25_6_1
    · exact s25_6_2
    · exact s25_6_3
    · exact s25_6_4
    · exact s25_6_5
    · exact s25_6_6
    · exact s25_6_7
  · exact List.all_eq_true.mp col25_7 v (List.mem_finRange v)
theorem col26_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 0 v) = true := by decide +kernel
theorem col26_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 1 v) = true := by decide +kernel
theorem col26_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 2 v) = true := by decide +kernel
theorem s26_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 0 = true := by decide +kernel
theorem s26_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 1 = true := by decide +kernel
theorem s26_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 2 = true := by decide +kernel
theorem s26_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 3 = true := by decide +kernel
theorem s26_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 4 = true := by decide +kernel
theorem s26_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 5 = true := by decide +kernel
theorem k26_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k26_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k26_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k26_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k26_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k26_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k26_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k26_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k26_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k26_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k26_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s26_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k26_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k26_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k26_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k26_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k26_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k26_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k26_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k26_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k26_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k26_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 3 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k26_3_6_130 k h.1 (by omega)
theorem s26_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 3 7 = true := by decide +kernel
theorem s26_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 0 = true := by decide +kernel
theorem s26_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 1 = true := by decide +kernel
theorem s26_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 2 = true := by decide +kernel
theorem s26_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 3 = true := by decide +kernel
theorem s26_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 4 = true := by decide +kernel
theorem s26_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 5 = true := by decide +kernel
theorem k26_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k26_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k26_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k26_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k26_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k26_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k26_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s26_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k26_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k26_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k26_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k26_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k26_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k26_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 4 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k26_4_6_126 k h.1 (by omega)
theorem s26_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 4 7 = true := by decide +kernel
theorem s26_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 0 = true := by decide +kernel
theorem s26_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 1 = true := by decide +kernel
theorem s26_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 2 = true := by decide +kernel
theorem s26_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 3 = true := by decide +kernel
theorem s26_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 4 = true := by decide +kernel
theorem s26_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 5 = true := by decide +kernel
theorem k26_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k26_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k26_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k26_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k26_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k26_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k26_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s26_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k26_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k26_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k26_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k26_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k26_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k26_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 5 6).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k26_5_6_126 k h.1 (by omega)
theorem s26_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 5 7 = true := by decide +kernel
theorem s26_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 0 = true := by decide +kernel
theorem s26_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 1 = true := by decide +kernel
theorem s26_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 2 = true := by decide +kernel
theorem s26_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 3 = true := by decide +kernel
theorem s26_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 4 = true := by decide +kernel
theorem s26_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 5 = true := by decide +kernel
theorem s26_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 6 = true := by decide +kernel
theorem k26_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k26_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k26_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k26_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k26_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s26_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k26_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k26_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k26_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k26_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 26) ((InDA1.TCasaD 3 6 7).getD (26 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k26_6_7_12 k h.1 (by omega)
theorem col26_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 7 v) = true := by decide +kernel
theorem col26 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 26) 26 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col26_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col26_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col26_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s26_3_0
    · exact s26_3_1
    · exact s26_3_2
    · exact s26_3_3
    · exact s26_3_4
    · exact s26_3_5
    · exact s26_3_6
    · exact s26_3_7
  · fin_cases v
    · exact s26_4_0
    · exact s26_4_1
    · exact s26_4_2
    · exact s26_4_3
    · exact s26_4_4
    · exact s26_4_5
    · exact s26_4_6
    · exact s26_4_7
  · fin_cases v
    · exact s26_5_0
    · exact s26_5_1
    · exact s26_5_2
    · exact s26_5_3
    · exact s26_5_4
    · exact s26_5_5
    · exact s26_5_6
    · exact s26_5_7
  · fin_cases v
    · exact s26_6_0
    · exact s26_6_1
    · exact s26_6_2
    · exact s26_6_3
    · exact s26_6_4
    · exact s26_6_5
    · exact s26_6_6
    · exact s26_6_7
  · exact List.all_eq_true.mp col26_7 v (List.mem_finRange v)
theorem col27_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 0 v) = true := by decide +kernel
theorem col27_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 1 v) = true := by decide +kernel
theorem col27_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 2 v) = true := by decide +kernel
theorem s27_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 0 = true := by decide +kernel
theorem s27_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 1 = true := by decide +kernel
theorem s27_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 2 = true := by decide +kernel
theorem s27_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 3 = true := by decide +kernel
theorem s27_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 4 = true := by decide +kernel
theorem s27_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 5 = true := by decide +kernel
theorem k27_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k27_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k27_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k27_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k27_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k27_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k27_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k27_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k27_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k27_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k27_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s27_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k27_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k27_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k27_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k27_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k27_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k27_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k27_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k27_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k27_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k27_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 3 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k27_3_6_130 k h.1 (by omega)
theorem s27_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 3 7 = true := by decide +kernel
theorem s27_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 0 = true := by decide +kernel
theorem s27_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 1 = true := by decide +kernel
theorem s27_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 2 = true := by decide +kernel
theorem s27_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 3 = true := by decide +kernel
theorem s27_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 4 = true := by decide +kernel
theorem s27_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 5 = true := by decide +kernel
theorem k27_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k27_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k27_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k27_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k27_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k27_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k27_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s27_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k27_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k27_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k27_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k27_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k27_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k27_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 4 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k27_4_6_126 k h.1 (by omega)
theorem s27_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 4 7 = true := by decide +kernel
theorem s27_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 0 = true := by decide +kernel
theorem s27_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 1 = true := by decide +kernel
theorem s27_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 2 = true := by decide +kernel
theorem s27_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 3 = true := by decide +kernel
theorem s27_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 4 = true := by decide +kernel
theorem s27_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 5 = true := by decide +kernel
theorem k27_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k27_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k27_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k27_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k27_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k27_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k27_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s27_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k27_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k27_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k27_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k27_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k27_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k27_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 5 6).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k27_5_6_126 k h.1 (by omega)
theorem s27_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 5 7 = true := by decide +kernel
theorem s27_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 0 = true := by decide +kernel
theorem s27_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 1 = true := by decide +kernel
theorem s27_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 2 = true := by decide +kernel
theorem s27_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 3 = true := by decide +kernel
theorem s27_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 4 = true := by decide +kernel
theorem s27_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 5 = true := by decide +kernel
theorem s27_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 6 = true := by decide +kernel
theorem k27_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k27_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k27_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k27_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k27_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s27_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k27_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k27_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k27_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k27_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 27) ((InDA1.TCasaD 3 6 7).getD (27 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k27_6_7_12 k h.1 (by omega)
theorem col27_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 7 v) = true := by decide +kernel
theorem col27 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 27) 27 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col27_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col27_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col27_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s27_3_0
    · exact s27_3_1
    · exact s27_3_2
    · exact s27_3_3
    · exact s27_3_4
    · exact s27_3_5
    · exact s27_3_6
    · exact s27_3_7
  · fin_cases v
    · exact s27_4_0
    · exact s27_4_1
    · exact s27_4_2
    · exact s27_4_3
    · exact s27_4_4
    · exact s27_4_5
    · exact s27_4_6
    · exact s27_4_7
  · fin_cases v
    · exact s27_5_0
    · exact s27_5_1
    · exact s27_5_2
    · exact s27_5_3
    · exact s27_5_4
    · exact s27_5_5
    · exact s27_5_6
    · exact s27_5_7
  · fin_cases v
    · exact s27_6_0
    · exact s27_6_1
    · exact s27_6_2
    · exact s27_6_3
    · exact s27_6_4
    · exact s27_6_5
    · exact s27_6_6
    · exact s27_6_7
  · exact List.all_eq_true.mp col27_7 v (List.mem_finRange v)
theorem col28_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 0 v) = true := by decide +kernel
theorem col28_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 1 v) = true := by decide +kernel
theorem col28_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 2 v) = true := by decide +kernel
theorem s28_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 0 = true := by decide +kernel
theorem s28_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 1 = true := by decide +kernel
theorem s28_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 2 = true := by decide +kernel
theorem s28_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 3 = true := by decide +kernel
theorem s28_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 4 = true := by decide +kernel
theorem s28_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 5 = true := by decide +kernel
theorem k28_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k28_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k28_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k28_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k28_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k28_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k28_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k28_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k28_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k28_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k28_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s28_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k28_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k28_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k28_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k28_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k28_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k28_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k28_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k28_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k28_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k28_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 3 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k28_3_6_130 k h.1 (by omega)
theorem s28_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 3 7 = true := by decide +kernel
theorem s28_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 0 = true := by decide +kernel
theorem s28_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 1 = true := by decide +kernel
theorem s28_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 2 = true := by decide +kernel
theorem s28_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 3 = true := by decide +kernel
theorem s28_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 4 = true := by decide +kernel
theorem s28_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 5 = true := by decide +kernel
theorem k28_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k28_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k28_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k28_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k28_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k28_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k28_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s28_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k28_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k28_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k28_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k28_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k28_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k28_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 4 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k28_4_6_126 k h.1 (by omega)
theorem s28_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 4 7 = true := by decide +kernel
theorem s28_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 0 = true := by decide +kernel
theorem s28_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 1 = true := by decide +kernel
theorem s28_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 2 = true := by decide +kernel
theorem s28_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 3 = true := by decide +kernel
theorem s28_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 4 = true := by decide +kernel
theorem s28_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 5 = true := by decide +kernel
theorem k28_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k28_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k28_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k28_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k28_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k28_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k28_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s28_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k28_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k28_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k28_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k28_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k28_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k28_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 5 6).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k28_5_6_126 k h.1 (by omega)
theorem s28_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 5 7 = true := by decide +kernel
theorem s28_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 0 = true := by decide +kernel
theorem s28_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 1 = true := by decide +kernel
theorem s28_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 2 = true := by decide +kernel
theorem s28_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 3 = true := by decide +kernel
theorem s28_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 4 = true := by decide +kernel
theorem s28_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 5 = true := by decide +kernel
theorem s28_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 6 = true := by decide +kernel
theorem k28_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k28_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k28_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k28_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k28_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s28_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k28_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k28_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k28_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k28_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 28) ((InDA1.TCasaD 3 6 7).getD (28 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k28_6_7_12 k h.1 (by omega)
theorem col28_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 7 v) = true := by decide +kernel
theorem col28 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 28) 28 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col28_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col28_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col28_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s28_3_0
    · exact s28_3_1
    · exact s28_3_2
    · exact s28_3_3
    · exact s28_3_4
    · exact s28_3_5
    · exact s28_3_6
    · exact s28_3_7
  · fin_cases v
    · exact s28_4_0
    · exact s28_4_1
    · exact s28_4_2
    · exact s28_4_3
    · exact s28_4_4
    · exact s28_4_5
    · exact s28_4_6
    · exact s28_4_7
  · fin_cases v
    · exact s28_5_0
    · exact s28_5_1
    · exact s28_5_2
    · exact s28_5_3
    · exact s28_5_4
    · exact s28_5_5
    · exact s28_5_6
    · exact s28_5_7
  · fin_cases v
    · exact s28_6_0
    · exact s28_6_1
    · exact s28_6_2
    · exact s28_6_3
    · exact s28_6_4
    · exact s28_6_5
    · exact s28_6_6
    · exact s28_6_7
  · exact List.all_eq_true.mp col28_7 v (List.mem_finRange v)
theorem col29_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 0 v) = true := by decide +kernel
theorem col29_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 1 v) = true := by decide +kernel
theorem col29_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 2 v) = true := by decide +kernel
theorem s29_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 0 = true := by decide +kernel
theorem s29_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 1 = true := by decide +kernel
theorem s29_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 2 = true := by decide +kernel
theorem s29_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 3 = true := by decide +kernel
theorem s29_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 4 = true := by decide +kernel
theorem s29_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 5 = true := by decide +kernel
theorem k29_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k29_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k29_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k29_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k29_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k29_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k29_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k29_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k29_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k29_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k29_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s29_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k29_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k29_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k29_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k29_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k29_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k29_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k29_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k29_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k29_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k29_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 3 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k29_3_6_130 k h.1 (by omega)
theorem s29_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 3 7 = true := by decide +kernel
theorem s29_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 0 = true := by decide +kernel
theorem s29_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 1 = true := by decide +kernel
theorem s29_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 2 = true := by decide +kernel
theorem s29_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 3 = true := by decide +kernel
theorem s29_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 4 = true := by decide +kernel
theorem s29_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 5 = true := by decide +kernel
theorem k29_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k29_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k29_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k29_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k29_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k29_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k29_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s29_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k29_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k29_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k29_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k29_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k29_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k29_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 4 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k29_4_6_126 k h.1 (by omega)
theorem s29_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 4 7 = true := by decide +kernel
theorem s29_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 0 = true := by decide +kernel
theorem s29_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 1 = true := by decide +kernel
theorem s29_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 2 = true := by decide +kernel
theorem s29_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 3 = true := by decide +kernel
theorem s29_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 4 = true := by decide +kernel
theorem s29_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 5 = true := by decide +kernel
theorem k29_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k29_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k29_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k29_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k29_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k29_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k29_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s29_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k29_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k29_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k29_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k29_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k29_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k29_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 5 6).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k29_5_6_126 k h.1 (by omega)
theorem s29_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 5 7 = true := by decide +kernel
theorem s29_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 0 = true := by decide +kernel
theorem s29_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 1 = true := by decide +kernel
theorem s29_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 2 = true := by decide +kernel
theorem s29_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 3 = true := by decide +kernel
theorem s29_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 4 = true := by decide +kernel
theorem s29_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 5 = true := by decide +kernel
theorem s29_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 6 = true := by decide +kernel
theorem k29_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k29_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k29_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k29_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k29_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s29_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k29_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k29_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k29_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k29_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 29) ((InDA1.TCasaD 3 6 7).getD (29 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k29_6_7_12 k h.1 (by omega)
theorem col29_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 7 v) = true := by decide +kernel
theorem col29 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 29) 29 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col29_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col29_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col29_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s29_3_0
    · exact s29_3_1
    · exact s29_3_2
    · exact s29_3_3
    · exact s29_3_4
    · exact s29_3_5
    · exact s29_3_6
    · exact s29_3_7
  · fin_cases v
    · exact s29_4_0
    · exact s29_4_1
    · exact s29_4_2
    · exact s29_4_3
    · exact s29_4_4
    · exact s29_4_5
    · exact s29_4_6
    · exact s29_4_7
  · fin_cases v
    · exact s29_5_0
    · exact s29_5_1
    · exact s29_5_2
    · exact s29_5_3
    · exact s29_5_4
    · exact s29_5_5
    · exact s29_5_6
    · exact s29_5_7
  · fin_cases v
    · exact s29_6_0
    · exact s29_6_1
    · exact s29_6_2
    · exact s29_6_3
    · exact s29_6_4
    · exact s29_6_5
    · exact s29_6_6
    · exact s29_6_7
  · exact List.all_eq_true.mp col29_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
