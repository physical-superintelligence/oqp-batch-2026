module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [10, 15). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col10_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 0 v) = true := by decide +kernel
theorem col10_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 1 v) = true := by decide +kernel
theorem col10_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 2 v) = true := by decide +kernel
theorem s10_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 0 = true := by decide +kernel
theorem s10_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 1 = true := by decide +kernel
theorem s10_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 2 = true := by decide +kernel
theorem s10_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 3 = true := by decide +kernel
theorem s10_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 4 = true := by decide +kernel
theorem s10_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 5 = true := by decide +kernel
theorem k10_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k10_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k10_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k10_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k10_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k10_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k10_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k10_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k10_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k10_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k10_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s10_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k10_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k10_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k10_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k10_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k10_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k10_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k10_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k10_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k10_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k10_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 3 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k10_3_6_130 k h.1 (by omega)
theorem s10_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 3 7 = true := by decide +kernel
theorem s10_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 0 = true := by decide +kernel
theorem s10_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 1 = true := by decide +kernel
theorem s10_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 2 = true := by decide +kernel
theorem s10_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 3 = true := by decide +kernel
theorem s10_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 4 = true := by decide +kernel
theorem s10_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 5 = true := by decide +kernel
theorem k10_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k10_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k10_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k10_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k10_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k10_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k10_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s10_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k10_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k10_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k10_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k10_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k10_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k10_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 4 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k10_4_6_126 k h.1 (by omega)
theorem s10_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 4 7 = true := by decide +kernel
theorem s10_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 0 = true := by decide +kernel
theorem s10_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 1 = true := by decide +kernel
theorem s10_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 2 = true := by decide +kernel
theorem s10_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 3 = true := by decide +kernel
theorem s10_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 4 = true := by decide +kernel
theorem s10_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 5 = true := by decide +kernel
theorem k10_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k10_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k10_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k10_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k10_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k10_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k10_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s10_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k10_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k10_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k10_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k10_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k10_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k10_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 5 6).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k10_5_6_126 k h.1 (by omega)
theorem s10_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 5 7 = true := by decide +kernel
theorem s10_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 0 = true := by decide +kernel
theorem s10_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 1 = true := by decide +kernel
theorem s10_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 2 = true := by decide +kernel
theorem s10_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 3 = true := by decide +kernel
theorem s10_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 4 = true := by decide +kernel
theorem s10_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 5 = true := by decide +kernel
theorem s10_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 6 = true := by decide +kernel
theorem k10_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k10_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k10_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k10_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k10_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s10_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k10_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k10_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k10_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k10_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 10) ((InDA1.TCasaD 3 6 7).getD (10 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k10_6_7_12 k h.1 (by omega)
theorem col10_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 7 v) = true := by decide +kernel
theorem col10 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 10) 10 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col10_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col10_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col10_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s10_3_0
    · exact s10_3_1
    · exact s10_3_2
    · exact s10_3_3
    · exact s10_3_4
    · exact s10_3_5
    · exact s10_3_6
    · exact s10_3_7
  · fin_cases v
    · exact s10_4_0
    · exact s10_4_1
    · exact s10_4_2
    · exact s10_4_3
    · exact s10_4_4
    · exact s10_4_5
    · exact s10_4_6
    · exact s10_4_7
  · fin_cases v
    · exact s10_5_0
    · exact s10_5_1
    · exact s10_5_2
    · exact s10_5_3
    · exact s10_5_4
    · exact s10_5_5
    · exact s10_5_6
    · exact s10_5_7
  · fin_cases v
    · exact s10_6_0
    · exact s10_6_1
    · exact s10_6_2
    · exact s10_6_3
    · exact s10_6_4
    · exact s10_6_5
    · exact s10_6_6
    · exact s10_6_7
  · exact List.all_eq_true.mp col10_7 v (List.mem_finRange v)
theorem col11_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 0 v) = true := by decide +kernel
theorem col11_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 1 v) = true := by decide +kernel
theorem col11_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 2 v) = true := by decide +kernel
theorem s11_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 0 = true := by decide +kernel
theorem s11_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 1 = true := by decide +kernel
theorem s11_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 2 = true := by decide +kernel
theorem s11_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 3 = true := by decide +kernel
theorem s11_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 4 = true := by decide +kernel
theorem s11_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 5 = true := by decide +kernel
theorem k11_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k11_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k11_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k11_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k11_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k11_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k11_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k11_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k11_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k11_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k11_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s11_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k11_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k11_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k11_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k11_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k11_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k11_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k11_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k11_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k11_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k11_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 3 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k11_3_6_130 k h.1 (by omega)
theorem s11_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 3 7 = true := by decide +kernel
theorem s11_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 0 = true := by decide +kernel
theorem s11_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 1 = true := by decide +kernel
theorem s11_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 2 = true := by decide +kernel
theorem s11_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 3 = true := by decide +kernel
theorem s11_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 4 = true := by decide +kernel
theorem s11_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 5 = true := by decide +kernel
theorem k11_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k11_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k11_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k11_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k11_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k11_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k11_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s11_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k11_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k11_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k11_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k11_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k11_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k11_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 4 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k11_4_6_126 k h.1 (by omega)
theorem s11_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 4 7 = true := by decide +kernel
theorem s11_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 0 = true := by decide +kernel
theorem s11_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 1 = true := by decide +kernel
theorem s11_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 2 = true := by decide +kernel
theorem s11_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 3 = true := by decide +kernel
theorem s11_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 4 = true := by decide +kernel
theorem s11_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 5 = true := by decide +kernel
theorem k11_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k11_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k11_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k11_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k11_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k11_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k11_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s11_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k11_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k11_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k11_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k11_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k11_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k11_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 5 6).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k11_5_6_126 k h.1 (by omega)
theorem s11_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 5 7 = true := by decide +kernel
theorem s11_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 0 = true := by decide +kernel
theorem s11_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 1 = true := by decide +kernel
theorem s11_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 2 = true := by decide +kernel
theorem s11_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 3 = true := by decide +kernel
theorem s11_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 4 = true := by decide +kernel
theorem s11_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 5 = true := by decide +kernel
theorem s11_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 6 = true := by decide +kernel
theorem k11_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k11_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k11_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k11_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k11_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s11_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k11_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k11_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k11_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k11_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 11) ((InDA1.TCasaD 3 6 7).getD (11 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k11_6_7_12 k h.1 (by omega)
theorem col11_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 7 v) = true := by decide +kernel
theorem col11 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 11) 11 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col11_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col11_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col11_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s11_3_0
    · exact s11_3_1
    · exact s11_3_2
    · exact s11_3_3
    · exact s11_3_4
    · exact s11_3_5
    · exact s11_3_6
    · exact s11_3_7
  · fin_cases v
    · exact s11_4_0
    · exact s11_4_1
    · exact s11_4_2
    · exact s11_4_3
    · exact s11_4_4
    · exact s11_4_5
    · exact s11_4_6
    · exact s11_4_7
  · fin_cases v
    · exact s11_5_0
    · exact s11_5_1
    · exact s11_5_2
    · exact s11_5_3
    · exact s11_5_4
    · exact s11_5_5
    · exact s11_5_6
    · exact s11_5_7
  · fin_cases v
    · exact s11_6_0
    · exact s11_6_1
    · exact s11_6_2
    · exact s11_6_3
    · exact s11_6_4
    · exact s11_6_5
    · exact s11_6_6
    · exact s11_6_7
  · exact List.all_eq_true.mp col11_7 v (List.mem_finRange v)
theorem col12_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 0 v) = true := by decide +kernel
theorem col12_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 1 v) = true := by decide +kernel
theorem col12_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 2 v) = true := by decide +kernel
theorem s12_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 0 = true := by decide +kernel
theorem s12_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 1 = true := by decide +kernel
theorem s12_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 2 = true := by decide +kernel
theorem s12_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 3 = true := by decide +kernel
theorem s12_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 4 = true := by decide +kernel
theorem s12_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 5 = true := by decide +kernel
theorem k12_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k12_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k12_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k12_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k12_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k12_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k12_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k12_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k12_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k12_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k12_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s12_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k12_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k12_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k12_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k12_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k12_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k12_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k12_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k12_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k12_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k12_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 3 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k12_3_6_130 k h.1 (by omega)
theorem s12_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 3 7 = true := by decide +kernel
theorem s12_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 0 = true := by decide +kernel
theorem s12_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 1 = true := by decide +kernel
theorem s12_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 2 = true := by decide +kernel
theorem s12_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 3 = true := by decide +kernel
theorem s12_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 4 = true := by decide +kernel
theorem s12_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 5 = true := by decide +kernel
theorem k12_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k12_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k12_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k12_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k12_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k12_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k12_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s12_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k12_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k12_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k12_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k12_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k12_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k12_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 4 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k12_4_6_126 k h.1 (by omega)
theorem s12_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 4 7 = true := by decide +kernel
theorem s12_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 0 = true := by decide +kernel
theorem s12_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 1 = true := by decide +kernel
theorem s12_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 2 = true := by decide +kernel
theorem s12_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 3 = true := by decide +kernel
theorem s12_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 4 = true := by decide +kernel
theorem s12_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 5 = true := by decide +kernel
theorem k12_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k12_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k12_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k12_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k12_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k12_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k12_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s12_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k12_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k12_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k12_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k12_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k12_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k12_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 5 6).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k12_5_6_126 k h.1 (by omega)
theorem s12_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 5 7 = true := by decide +kernel
theorem s12_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 0 = true := by decide +kernel
theorem s12_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 1 = true := by decide +kernel
theorem s12_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 2 = true := by decide +kernel
theorem s12_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 3 = true := by decide +kernel
theorem s12_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 4 = true := by decide +kernel
theorem s12_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 5 = true := by decide +kernel
theorem s12_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 6 = true := by decide +kernel
theorem k12_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k12_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k12_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k12_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k12_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s12_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k12_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k12_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k12_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k12_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 12) ((InDA1.TCasaD 3 6 7).getD (12 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k12_6_7_12 k h.1 (by omega)
theorem col12_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 7 v) = true := by decide +kernel
theorem col12 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 12) 12 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col12_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col12_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col12_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s12_3_0
    · exact s12_3_1
    · exact s12_3_2
    · exact s12_3_3
    · exact s12_3_4
    · exact s12_3_5
    · exact s12_3_6
    · exact s12_3_7
  · fin_cases v
    · exact s12_4_0
    · exact s12_4_1
    · exact s12_4_2
    · exact s12_4_3
    · exact s12_4_4
    · exact s12_4_5
    · exact s12_4_6
    · exact s12_4_7
  · fin_cases v
    · exact s12_5_0
    · exact s12_5_1
    · exact s12_5_2
    · exact s12_5_3
    · exact s12_5_4
    · exact s12_5_5
    · exact s12_5_6
    · exact s12_5_7
  · fin_cases v
    · exact s12_6_0
    · exact s12_6_1
    · exact s12_6_2
    · exact s12_6_3
    · exact s12_6_4
    · exact s12_6_5
    · exact s12_6_6
    · exact s12_6_7
  · exact List.all_eq_true.mp col12_7 v (List.mem_finRange v)
theorem col13_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 0 v) = true := by decide +kernel
theorem col13_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 1 v) = true := by decide +kernel
theorem col13_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 2 v) = true := by decide +kernel
theorem s13_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 0 = true := by decide +kernel
theorem s13_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 1 = true := by decide +kernel
theorem s13_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 2 = true := by decide +kernel
theorem s13_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 3 = true := by decide +kernel
theorem s13_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 4 = true := by decide +kernel
theorem s13_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 5 = true := by decide +kernel
theorem k13_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k13_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k13_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k13_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k13_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k13_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k13_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k13_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k13_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k13_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k13_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s13_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k13_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k13_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k13_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k13_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k13_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k13_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k13_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k13_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k13_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k13_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 3 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k13_3_6_130 k h.1 (by omega)
theorem s13_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 3 7 = true := by decide +kernel
theorem s13_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 0 = true := by decide +kernel
theorem s13_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 1 = true := by decide +kernel
theorem s13_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 2 = true := by decide +kernel
theorem s13_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 3 = true := by decide +kernel
theorem s13_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 4 = true := by decide +kernel
theorem s13_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 5 = true := by decide +kernel
theorem k13_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k13_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k13_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k13_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k13_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k13_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k13_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s13_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k13_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k13_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k13_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k13_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k13_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k13_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 4 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k13_4_6_126 k h.1 (by omega)
theorem s13_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 4 7 = true := by decide +kernel
theorem s13_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 0 = true := by decide +kernel
theorem s13_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 1 = true := by decide +kernel
theorem s13_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 2 = true := by decide +kernel
theorem s13_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 3 = true := by decide +kernel
theorem s13_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 4 = true := by decide +kernel
theorem s13_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 5 = true := by decide +kernel
theorem k13_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k13_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k13_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k13_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k13_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k13_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k13_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s13_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k13_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k13_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k13_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k13_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k13_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k13_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 5 6).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k13_5_6_126 k h.1 (by omega)
theorem s13_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 5 7 = true := by decide +kernel
theorem s13_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 0 = true := by decide +kernel
theorem s13_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 1 = true := by decide +kernel
theorem s13_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 2 = true := by decide +kernel
theorem s13_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 3 = true := by decide +kernel
theorem s13_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 4 = true := by decide +kernel
theorem s13_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 5 = true := by decide +kernel
theorem s13_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 6 = true := by decide +kernel
theorem k13_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k13_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k13_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k13_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k13_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s13_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k13_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k13_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k13_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k13_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 13) ((InDA1.TCasaD 3 6 7).getD (13 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k13_6_7_12 k h.1 (by omega)
theorem col13_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 7 v) = true := by decide +kernel
theorem col13 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 13) 13 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col13_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col13_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col13_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s13_3_0
    · exact s13_3_1
    · exact s13_3_2
    · exact s13_3_3
    · exact s13_3_4
    · exact s13_3_5
    · exact s13_3_6
    · exact s13_3_7
  · fin_cases v
    · exact s13_4_0
    · exact s13_4_1
    · exact s13_4_2
    · exact s13_4_3
    · exact s13_4_4
    · exact s13_4_5
    · exact s13_4_6
    · exact s13_4_7
  · fin_cases v
    · exact s13_5_0
    · exact s13_5_1
    · exact s13_5_2
    · exact s13_5_3
    · exact s13_5_4
    · exact s13_5_5
    · exact s13_5_6
    · exact s13_5_7
  · fin_cases v
    · exact s13_6_0
    · exact s13_6_1
    · exact s13_6_2
    · exact s13_6_3
    · exact s13_6_4
    · exact s13_6_5
    · exact s13_6_6
    · exact s13_6_7
  · exact List.all_eq_true.mp col13_7 v (List.mem_finRange v)
theorem col14_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 0 v) = true := by decide +kernel
theorem col14_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 1 v) = true := by decide +kernel
theorem col14_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 2 v) = true := by decide +kernel
theorem s14_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 0 = true := by decide +kernel
theorem s14_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 1 = true := by decide +kernel
theorem s14_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 2 = true := by decide +kernel
theorem s14_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 3 = true := by decide +kernel
theorem s14_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 4 = true := by decide +kernel
theorem s14_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 5 = true := by decide +kernel
theorem k14_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k14_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k14_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k14_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k14_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k14_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k14_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k14_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k14_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k14_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k14_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s14_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k14_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k14_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k14_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k14_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k14_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k14_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k14_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k14_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k14_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k14_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 3 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k14_3_6_130 k h.1 (by omega)
theorem s14_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 3 7 = true := by decide +kernel
theorem s14_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 0 = true := by decide +kernel
theorem s14_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 1 = true := by decide +kernel
theorem s14_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 2 = true := by decide +kernel
theorem s14_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 3 = true := by decide +kernel
theorem s14_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 4 = true := by decide +kernel
theorem s14_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 5 = true := by decide +kernel
theorem k14_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k14_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k14_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k14_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k14_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k14_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k14_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s14_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k14_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k14_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k14_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k14_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k14_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k14_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 4 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k14_4_6_126 k h.1 (by omega)
theorem s14_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 4 7 = true := by decide +kernel
theorem s14_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 0 = true := by decide +kernel
theorem s14_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 1 = true := by decide +kernel
theorem s14_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 2 = true := by decide +kernel
theorem s14_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 3 = true := by decide +kernel
theorem s14_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 4 = true := by decide +kernel
theorem s14_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 5 = true := by decide +kernel
theorem k14_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k14_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k14_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k14_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k14_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k14_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k14_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s14_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k14_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k14_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k14_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k14_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k14_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k14_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 5 6).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k14_5_6_126 k h.1 (by omega)
theorem s14_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 5 7 = true := by decide +kernel
theorem s14_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 0 = true := by decide +kernel
theorem s14_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 1 = true := by decide +kernel
theorem s14_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 2 = true := by decide +kernel
theorem s14_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 3 = true := by decide +kernel
theorem s14_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 4 = true := by decide +kernel
theorem s14_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 5 = true := by decide +kernel
theorem s14_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 6 = true := by decide +kernel
theorem k14_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k14_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k14_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k14_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k14_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s14_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k14_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k14_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k14_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k14_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 14) ((InDA1.TCasaD 3 6 7).getD (14 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k14_6_7_12 k h.1 (by omega)
theorem col14_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 7 v) = true := by decide +kernel
theorem col14 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 14) 14 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col14_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col14_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col14_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s14_3_0
    · exact s14_3_1
    · exact s14_3_2
    · exact s14_3_3
    · exact s14_3_4
    · exact s14_3_5
    · exact s14_3_6
    · exact s14_3_7
  · fin_cases v
    · exact s14_4_0
    · exact s14_4_1
    · exact s14_4_2
    · exact s14_4_3
    · exact s14_4_4
    · exact s14_4_5
    · exact s14_4_6
    · exact s14_4_7
  · fin_cases v
    · exact s14_5_0
    · exact s14_5_1
    · exact s14_5_2
    · exact s14_5_3
    · exact s14_5_4
    · exact s14_5_5
    · exact s14_5_6
    · exact s14_5_7
  · fin_cases v
    · exact s14_6_0
    · exact s14_6_1
    · exact s14_6_2
    · exact s14_6_3
    · exact s14_6_4
    · exact s14_6_5
    · exact s14_6_6
    · exact s14_6_7
  · exact List.all_eq_true.mp col14_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
