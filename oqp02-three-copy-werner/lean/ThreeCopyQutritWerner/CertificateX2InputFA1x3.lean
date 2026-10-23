module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [15, 20). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col15_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 0 v) = true := by decide +kernel
theorem col15_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 1 v) = true := by decide +kernel
theorem col15_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 2 v) = true := by decide +kernel
theorem s15_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 0 = true := by decide +kernel
theorem s15_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 1 = true := by decide +kernel
theorem s15_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 2 = true := by decide +kernel
theorem s15_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 3 = true := by decide +kernel
theorem s15_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 4 = true := by decide +kernel
theorem s15_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 5 = true := by decide +kernel
theorem k15_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k15_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k15_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k15_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k15_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k15_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k15_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k15_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k15_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k15_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k15_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s15_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k15_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k15_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k15_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k15_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k15_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k15_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k15_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k15_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k15_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k15_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 3 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k15_3_6_130 k h.1 (by omega)
theorem s15_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 3 7 = true := by decide +kernel
theorem s15_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 0 = true := by decide +kernel
theorem s15_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 1 = true := by decide +kernel
theorem s15_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 2 = true := by decide +kernel
theorem s15_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 3 = true := by decide +kernel
theorem s15_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 4 = true := by decide +kernel
theorem s15_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 5 = true := by decide +kernel
theorem k15_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k15_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k15_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k15_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k15_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k15_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k15_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s15_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k15_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k15_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k15_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k15_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k15_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k15_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 4 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k15_4_6_126 k h.1 (by omega)
theorem s15_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 4 7 = true := by decide +kernel
theorem s15_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 0 = true := by decide +kernel
theorem s15_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 1 = true := by decide +kernel
theorem s15_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 2 = true := by decide +kernel
theorem s15_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 3 = true := by decide +kernel
theorem s15_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 4 = true := by decide +kernel
theorem s15_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 5 = true := by decide +kernel
theorem k15_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k15_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k15_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k15_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k15_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k15_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k15_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s15_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k15_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k15_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k15_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k15_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k15_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k15_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 5 6).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k15_5_6_126 k h.1 (by omega)
theorem s15_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 5 7 = true := by decide +kernel
theorem s15_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 0 = true := by decide +kernel
theorem s15_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 1 = true := by decide +kernel
theorem s15_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 2 = true := by decide +kernel
theorem s15_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 3 = true := by decide +kernel
theorem s15_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 4 = true := by decide +kernel
theorem s15_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 5 = true := by decide +kernel
theorem s15_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 6 = true := by decide +kernel
theorem k15_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k15_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k15_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k15_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k15_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s15_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k15_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k15_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k15_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k15_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 15) ((InDA1.TCasaD 3 6 7).getD (15 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k15_6_7_12 k h.1 (by omega)
theorem col15_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 7 v) = true := by decide +kernel
theorem col15 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 15) 15 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col15_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col15_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col15_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s15_3_0
    · exact s15_3_1
    · exact s15_3_2
    · exact s15_3_3
    · exact s15_3_4
    · exact s15_3_5
    · exact s15_3_6
    · exact s15_3_7
  · fin_cases v
    · exact s15_4_0
    · exact s15_4_1
    · exact s15_4_2
    · exact s15_4_3
    · exact s15_4_4
    · exact s15_4_5
    · exact s15_4_6
    · exact s15_4_7
  · fin_cases v
    · exact s15_5_0
    · exact s15_5_1
    · exact s15_5_2
    · exact s15_5_3
    · exact s15_5_4
    · exact s15_5_5
    · exact s15_5_6
    · exact s15_5_7
  · fin_cases v
    · exact s15_6_0
    · exact s15_6_1
    · exact s15_6_2
    · exact s15_6_3
    · exact s15_6_4
    · exact s15_6_5
    · exact s15_6_6
    · exact s15_6_7
  · exact List.all_eq_true.mp col15_7 v (List.mem_finRange v)
theorem col16_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 0 v) = true := by decide +kernel
theorem col16_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 1 v) = true := by decide +kernel
theorem col16_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 2 v) = true := by decide +kernel
theorem s16_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 0 = true := by decide +kernel
theorem s16_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 1 = true := by decide +kernel
theorem s16_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 2 = true := by decide +kernel
theorem s16_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 3 = true := by decide +kernel
theorem s16_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 4 = true := by decide +kernel
theorem s16_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 5 = true := by decide +kernel
theorem k16_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k16_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k16_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k16_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k16_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k16_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k16_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k16_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k16_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k16_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k16_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s16_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k16_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k16_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k16_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k16_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k16_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k16_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k16_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k16_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k16_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k16_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 3 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k16_3_6_130 k h.1 (by omega)
theorem s16_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 3 7 = true := by decide +kernel
theorem s16_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 0 = true := by decide +kernel
theorem s16_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 1 = true := by decide +kernel
theorem s16_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 2 = true := by decide +kernel
theorem s16_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 3 = true := by decide +kernel
theorem s16_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 4 = true := by decide +kernel
theorem s16_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 5 = true := by decide +kernel
theorem k16_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k16_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k16_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k16_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k16_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k16_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k16_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s16_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k16_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k16_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k16_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k16_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k16_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k16_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 4 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k16_4_6_126 k h.1 (by omega)
theorem s16_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 4 7 = true := by decide +kernel
theorem s16_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 0 = true := by decide +kernel
theorem s16_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 1 = true := by decide +kernel
theorem s16_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 2 = true := by decide +kernel
theorem s16_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 3 = true := by decide +kernel
theorem s16_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 4 = true := by decide +kernel
theorem s16_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 5 = true := by decide +kernel
theorem k16_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k16_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k16_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k16_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k16_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k16_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k16_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s16_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k16_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k16_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k16_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k16_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k16_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k16_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 5 6).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k16_5_6_126 k h.1 (by omega)
theorem s16_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 5 7 = true := by decide +kernel
theorem s16_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 0 = true := by decide +kernel
theorem s16_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 1 = true := by decide +kernel
theorem s16_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 2 = true := by decide +kernel
theorem s16_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 3 = true := by decide +kernel
theorem s16_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 4 = true := by decide +kernel
theorem s16_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 5 = true := by decide +kernel
theorem s16_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 6 = true := by decide +kernel
theorem k16_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k16_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k16_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k16_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k16_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s16_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k16_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k16_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k16_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k16_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 16) ((InDA1.TCasaD 3 6 7).getD (16 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k16_6_7_12 k h.1 (by omega)
theorem col16_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 7 v) = true := by decide +kernel
theorem col16 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 16) 16 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col16_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col16_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col16_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s16_3_0
    · exact s16_3_1
    · exact s16_3_2
    · exact s16_3_3
    · exact s16_3_4
    · exact s16_3_5
    · exact s16_3_6
    · exact s16_3_7
  · fin_cases v
    · exact s16_4_0
    · exact s16_4_1
    · exact s16_4_2
    · exact s16_4_3
    · exact s16_4_4
    · exact s16_4_5
    · exact s16_4_6
    · exact s16_4_7
  · fin_cases v
    · exact s16_5_0
    · exact s16_5_1
    · exact s16_5_2
    · exact s16_5_3
    · exact s16_5_4
    · exact s16_5_5
    · exact s16_5_6
    · exact s16_5_7
  · fin_cases v
    · exact s16_6_0
    · exact s16_6_1
    · exact s16_6_2
    · exact s16_6_3
    · exact s16_6_4
    · exact s16_6_5
    · exact s16_6_6
    · exact s16_6_7
  · exact List.all_eq_true.mp col16_7 v (List.mem_finRange v)
theorem col17_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 0 v) = true := by decide +kernel
theorem col17_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 1 v) = true := by decide +kernel
theorem col17_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 2 v) = true := by decide +kernel
theorem s17_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 0 = true := by decide +kernel
theorem s17_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 1 = true := by decide +kernel
theorem s17_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 2 = true := by decide +kernel
theorem s17_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 3 = true := by decide +kernel
theorem s17_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 4 = true := by decide +kernel
theorem s17_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 5 = true := by decide +kernel
theorem k17_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k17_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k17_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k17_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k17_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k17_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k17_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k17_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k17_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k17_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k17_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s17_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k17_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k17_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k17_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k17_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k17_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k17_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k17_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k17_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k17_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k17_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 3 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k17_3_6_130 k h.1 (by omega)
theorem s17_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 3 7 = true := by decide +kernel
theorem s17_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 0 = true := by decide +kernel
theorem s17_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 1 = true := by decide +kernel
theorem s17_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 2 = true := by decide +kernel
theorem s17_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 3 = true := by decide +kernel
theorem s17_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 4 = true := by decide +kernel
theorem s17_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 5 = true := by decide +kernel
theorem k17_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k17_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k17_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k17_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k17_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k17_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k17_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s17_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k17_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k17_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k17_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k17_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k17_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k17_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 4 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k17_4_6_126 k h.1 (by omega)
theorem s17_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 4 7 = true := by decide +kernel
theorem s17_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 0 = true := by decide +kernel
theorem s17_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 1 = true := by decide +kernel
theorem s17_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 2 = true := by decide +kernel
theorem s17_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 3 = true := by decide +kernel
theorem s17_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 4 = true := by decide +kernel
theorem s17_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 5 = true := by decide +kernel
theorem k17_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k17_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k17_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k17_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k17_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k17_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k17_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s17_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k17_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k17_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k17_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k17_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k17_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k17_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 5 6).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k17_5_6_126 k h.1 (by omega)
theorem s17_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 5 7 = true := by decide +kernel
theorem s17_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 0 = true := by decide +kernel
theorem s17_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 1 = true := by decide +kernel
theorem s17_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 2 = true := by decide +kernel
theorem s17_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 3 = true := by decide +kernel
theorem s17_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 4 = true := by decide +kernel
theorem s17_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 5 = true := by decide +kernel
theorem s17_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 6 = true := by decide +kernel
theorem k17_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k17_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k17_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k17_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k17_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s17_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k17_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k17_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k17_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k17_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 17) ((InDA1.TCasaD 3 6 7).getD (17 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k17_6_7_12 k h.1 (by omega)
theorem col17_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 7 v) = true := by decide +kernel
theorem col17 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 17) 17 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col17_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col17_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col17_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s17_3_0
    · exact s17_3_1
    · exact s17_3_2
    · exact s17_3_3
    · exact s17_3_4
    · exact s17_3_5
    · exact s17_3_6
    · exact s17_3_7
  · fin_cases v
    · exact s17_4_0
    · exact s17_4_1
    · exact s17_4_2
    · exact s17_4_3
    · exact s17_4_4
    · exact s17_4_5
    · exact s17_4_6
    · exact s17_4_7
  · fin_cases v
    · exact s17_5_0
    · exact s17_5_1
    · exact s17_5_2
    · exact s17_5_3
    · exact s17_5_4
    · exact s17_5_5
    · exact s17_5_6
    · exact s17_5_7
  · fin_cases v
    · exact s17_6_0
    · exact s17_6_1
    · exact s17_6_2
    · exact s17_6_3
    · exact s17_6_4
    · exact s17_6_5
    · exact s17_6_6
    · exact s17_6_7
  · exact List.all_eq_true.mp col17_7 v (List.mem_finRange v)
theorem col18_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 0 v) = true := by decide +kernel
theorem col18_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 1 v) = true := by decide +kernel
theorem col18_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 2 v) = true := by decide +kernel
theorem s18_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 0 = true := by decide +kernel
theorem s18_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 1 = true := by decide +kernel
theorem s18_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 2 = true := by decide +kernel
theorem s18_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 3 = true := by decide +kernel
theorem s18_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 4 = true := by decide +kernel
theorem s18_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 5 = true := by decide +kernel
theorem k18_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k18_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k18_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k18_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k18_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k18_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k18_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k18_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k18_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k18_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k18_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s18_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k18_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k18_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k18_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k18_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k18_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k18_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k18_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k18_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k18_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k18_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 3 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k18_3_6_130 k h.1 (by omega)
theorem s18_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 3 7 = true := by decide +kernel
theorem s18_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 0 = true := by decide +kernel
theorem s18_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 1 = true := by decide +kernel
theorem s18_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 2 = true := by decide +kernel
theorem s18_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 3 = true := by decide +kernel
theorem s18_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 4 = true := by decide +kernel
theorem s18_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 5 = true := by decide +kernel
theorem k18_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k18_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k18_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k18_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k18_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k18_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k18_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s18_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k18_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k18_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k18_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k18_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k18_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k18_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 4 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k18_4_6_126 k h.1 (by omega)
theorem s18_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 4 7 = true := by decide +kernel
theorem s18_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 0 = true := by decide +kernel
theorem s18_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 1 = true := by decide +kernel
theorem s18_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 2 = true := by decide +kernel
theorem s18_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 3 = true := by decide +kernel
theorem s18_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 4 = true := by decide +kernel
theorem s18_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 5 = true := by decide +kernel
theorem k18_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k18_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k18_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k18_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k18_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k18_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k18_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s18_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k18_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k18_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k18_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k18_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k18_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k18_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 5 6).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k18_5_6_126 k h.1 (by omega)
theorem s18_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 5 7 = true := by decide +kernel
theorem s18_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 0 = true := by decide +kernel
theorem s18_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 1 = true := by decide +kernel
theorem s18_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 2 = true := by decide +kernel
theorem s18_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 3 = true := by decide +kernel
theorem s18_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 4 = true := by decide +kernel
theorem s18_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 5 = true := by decide +kernel
theorem s18_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 6 = true := by decide +kernel
theorem k18_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k18_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k18_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k18_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k18_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s18_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k18_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k18_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k18_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k18_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 18) ((InDA1.TCasaD 3 6 7).getD (18 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k18_6_7_12 k h.1 (by omega)
theorem col18_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 7 v) = true := by decide +kernel
theorem col18 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 18) 18 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col18_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col18_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col18_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s18_3_0
    · exact s18_3_1
    · exact s18_3_2
    · exact s18_3_3
    · exact s18_3_4
    · exact s18_3_5
    · exact s18_3_6
    · exact s18_3_7
  · fin_cases v
    · exact s18_4_0
    · exact s18_4_1
    · exact s18_4_2
    · exact s18_4_3
    · exact s18_4_4
    · exact s18_4_5
    · exact s18_4_6
    · exact s18_4_7
  · fin_cases v
    · exact s18_5_0
    · exact s18_5_1
    · exact s18_5_2
    · exact s18_5_3
    · exact s18_5_4
    · exact s18_5_5
    · exact s18_5_6
    · exact s18_5_7
  · fin_cases v
    · exact s18_6_0
    · exact s18_6_1
    · exact s18_6_2
    · exact s18_6_3
    · exact s18_6_4
    · exact s18_6_5
    · exact s18_6_6
    · exact s18_6_7
  · exact List.all_eq_true.mp col18_7 v (List.mem_finRange v)
theorem col19_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 0 v) = true := by decide +kernel
theorem col19_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 1 v) = true := by decide +kernel
theorem col19_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 2 v) = true := by decide +kernel
theorem s19_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 0 = true := by decide +kernel
theorem s19_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 1 = true := by decide +kernel
theorem s19_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 2 = true := by decide +kernel
theorem s19_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 3 = true := by decide +kernel
theorem s19_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 4 = true := by decide +kernel
theorem s19_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 5 = true := by decide +kernel
theorem k19_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k19_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k19_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k19_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k19_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k19_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k19_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k19_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k19_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k19_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k19_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s19_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k19_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k19_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k19_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k19_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k19_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k19_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k19_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k19_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k19_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k19_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 3 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k19_3_6_130 k h.1 (by omega)
theorem s19_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 3 7 = true := by decide +kernel
theorem s19_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 0 = true := by decide +kernel
theorem s19_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 1 = true := by decide +kernel
theorem s19_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 2 = true := by decide +kernel
theorem s19_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 3 = true := by decide +kernel
theorem s19_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 4 = true := by decide +kernel
theorem s19_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 5 = true := by decide +kernel
theorem k19_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k19_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k19_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k19_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k19_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k19_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k19_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s19_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k19_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k19_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k19_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k19_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k19_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k19_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 4 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k19_4_6_126 k h.1 (by omega)
theorem s19_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 4 7 = true := by decide +kernel
theorem s19_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 0 = true := by decide +kernel
theorem s19_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 1 = true := by decide +kernel
theorem s19_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 2 = true := by decide +kernel
theorem s19_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 3 = true := by decide +kernel
theorem s19_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 4 = true := by decide +kernel
theorem s19_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 5 = true := by decide +kernel
theorem k19_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k19_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k19_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k19_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k19_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k19_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k19_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s19_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k19_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k19_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k19_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k19_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k19_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k19_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 5 6).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k19_5_6_126 k h.1 (by omega)
theorem s19_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 5 7 = true := by decide +kernel
theorem s19_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 0 = true := by decide +kernel
theorem s19_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 1 = true := by decide +kernel
theorem s19_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 2 = true := by decide +kernel
theorem s19_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 3 = true := by decide +kernel
theorem s19_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 4 = true := by decide +kernel
theorem s19_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 5 = true := by decide +kernel
theorem s19_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 6 = true := by decide +kernel
theorem k19_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k19_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k19_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k19_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k19_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s19_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k19_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k19_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k19_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k19_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 19) ((InDA1.TCasaD 3 6 7).getD (19 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k19_6_7_12 k h.1 (by omega)
theorem col19_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 7 v) = true := by decide +kernel
theorem col19 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 19) 19 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col19_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col19_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col19_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s19_3_0
    · exact s19_3_1
    · exact s19_3_2
    · exact s19_3_3
    · exact s19_3_4
    · exact s19_3_5
    · exact s19_3_6
    · exact s19_3_7
  · fin_cases v
    · exact s19_4_0
    · exact s19_4_1
    · exact s19_4_2
    · exact s19_4_3
    · exact s19_4_4
    · exact s19_4_5
    · exact s19_4_6
    · exact s19_4_7
  · fin_cases v
    · exact s19_5_0
    · exact s19_5_1
    · exact s19_5_2
    · exact s19_5_3
    · exact s19_5_4
    · exact s19_5_5
    · exact s19_5_6
    · exact s19_5_7
  · fin_cases v
    · exact s19_6_0
    · exact s19_6_1
    · exact s19_6_2
    · exact s19_6_3
    · exact s19_6_4
    · exact s19_6_5
    · exact s19_6_6
    · exact s19_6_7
  · exact List.all_eq_true.mp col19_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
