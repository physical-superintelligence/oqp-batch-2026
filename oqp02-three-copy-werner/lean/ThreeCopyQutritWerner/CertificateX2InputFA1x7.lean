module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [35, 40). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col35_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 0 v) = true := by decide +kernel
theorem col35_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 1 v) = true := by decide +kernel
theorem col35_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 2 v) = true := by decide +kernel
theorem s35_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 0 = true := by decide +kernel
theorem s35_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 1 = true := by decide +kernel
theorem s35_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 2 = true := by decide +kernel
theorem s35_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 3 = true := by decide +kernel
theorem s35_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 4 = true := by decide +kernel
theorem s35_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 5 = true := by decide +kernel
theorem k35_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k35_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k35_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k35_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k35_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k35_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k35_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k35_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k35_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k35_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k35_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s35_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k35_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k35_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k35_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k35_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k35_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k35_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k35_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k35_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k35_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k35_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 3 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k35_3_6_130 k h.1 (by omega)
theorem s35_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 3 7 = true := by decide +kernel
theorem s35_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 0 = true := by decide +kernel
theorem s35_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 1 = true := by decide +kernel
theorem s35_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 2 = true := by decide +kernel
theorem s35_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 3 = true := by decide +kernel
theorem s35_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 4 = true := by decide +kernel
theorem s35_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 5 = true := by decide +kernel
theorem k35_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k35_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k35_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k35_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k35_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k35_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k35_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s35_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k35_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k35_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k35_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k35_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k35_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k35_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 4 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k35_4_6_126 k h.1 (by omega)
theorem s35_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 4 7 = true := by decide +kernel
theorem s35_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 0 = true := by decide +kernel
theorem s35_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 1 = true := by decide +kernel
theorem s35_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 2 = true := by decide +kernel
theorem s35_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 3 = true := by decide +kernel
theorem s35_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 4 = true := by decide +kernel
theorem s35_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 5 = true := by decide +kernel
theorem k35_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k35_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k35_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k35_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k35_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k35_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k35_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s35_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k35_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k35_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k35_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k35_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k35_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k35_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 5 6).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k35_5_6_126 k h.1 (by omega)
theorem s35_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 5 7 = true := by decide +kernel
theorem s35_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 0 = true := by decide +kernel
theorem s35_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 1 = true := by decide +kernel
theorem s35_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 2 = true := by decide +kernel
theorem s35_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 3 = true := by decide +kernel
theorem s35_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 4 = true := by decide +kernel
theorem s35_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 5 = true := by decide +kernel
theorem s35_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 6 = true := by decide +kernel
theorem k35_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k35_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k35_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k35_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k35_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s35_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k35_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k35_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k35_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k35_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 35) ((InDA1.TCasaD 3 6 7).getD (35 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k35_6_7_12 k h.1 (by omega)
theorem col35_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 7 v) = true := by decide +kernel
theorem col35 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 35) 35 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col35_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col35_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col35_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s35_3_0
    · exact s35_3_1
    · exact s35_3_2
    · exact s35_3_3
    · exact s35_3_4
    · exact s35_3_5
    · exact s35_3_6
    · exact s35_3_7
  · fin_cases v
    · exact s35_4_0
    · exact s35_4_1
    · exact s35_4_2
    · exact s35_4_3
    · exact s35_4_4
    · exact s35_4_5
    · exact s35_4_6
    · exact s35_4_7
  · fin_cases v
    · exact s35_5_0
    · exact s35_5_1
    · exact s35_5_2
    · exact s35_5_3
    · exact s35_5_4
    · exact s35_5_5
    · exact s35_5_6
    · exact s35_5_7
  · fin_cases v
    · exact s35_6_0
    · exact s35_6_1
    · exact s35_6_2
    · exact s35_6_3
    · exact s35_6_4
    · exact s35_6_5
    · exact s35_6_6
    · exact s35_6_7
  · exact List.all_eq_true.mp col35_7 v (List.mem_finRange v)
theorem col36_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 0 v) = true := by decide +kernel
theorem col36_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 1 v) = true := by decide +kernel
theorem col36_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 2 v) = true := by decide +kernel
theorem s36_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 0 = true := by decide +kernel
theorem s36_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 1 = true := by decide +kernel
theorem s36_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 2 = true := by decide +kernel
theorem s36_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 3 = true := by decide +kernel
theorem s36_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 4 = true := by decide +kernel
theorem s36_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 5 = true := by decide +kernel
theorem k36_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k36_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k36_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k36_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k36_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k36_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k36_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k36_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k36_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k36_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k36_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s36_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k36_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k36_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k36_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k36_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k36_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k36_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k36_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k36_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k36_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k36_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 3 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k36_3_6_130 k h.1 (by omega)
theorem s36_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 3 7 = true := by decide +kernel
theorem s36_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 0 = true := by decide +kernel
theorem s36_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 1 = true := by decide +kernel
theorem s36_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 2 = true := by decide +kernel
theorem s36_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 3 = true := by decide +kernel
theorem s36_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 4 = true := by decide +kernel
theorem s36_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 5 = true := by decide +kernel
theorem k36_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k36_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k36_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k36_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k36_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k36_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k36_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s36_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k36_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k36_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k36_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k36_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k36_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k36_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 4 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k36_4_6_126 k h.1 (by omega)
theorem s36_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 4 7 = true := by decide +kernel
theorem s36_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 0 = true := by decide +kernel
theorem s36_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 1 = true := by decide +kernel
theorem s36_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 2 = true := by decide +kernel
theorem s36_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 3 = true := by decide +kernel
theorem s36_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 4 = true := by decide +kernel
theorem s36_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 5 = true := by decide +kernel
theorem k36_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k36_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k36_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k36_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k36_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k36_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k36_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s36_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k36_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k36_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k36_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k36_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k36_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k36_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 5 6).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k36_5_6_126 k h.1 (by omega)
theorem s36_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 5 7 = true := by decide +kernel
theorem s36_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 0 = true := by decide +kernel
theorem s36_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 1 = true := by decide +kernel
theorem s36_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 2 = true := by decide +kernel
theorem s36_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 3 = true := by decide +kernel
theorem s36_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 4 = true := by decide +kernel
theorem s36_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 5 = true := by decide +kernel
theorem s36_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 6 = true := by decide +kernel
theorem k36_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k36_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k36_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k36_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k36_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s36_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k36_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k36_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k36_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k36_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 36) ((InDA1.TCasaD 3 6 7).getD (36 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k36_6_7_12 k h.1 (by omega)
theorem col36_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 7 v) = true := by decide +kernel
theorem col36 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 36) 36 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col36_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col36_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col36_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s36_3_0
    · exact s36_3_1
    · exact s36_3_2
    · exact s36_3_3
    · exact s36_3_4
    · exact s36_3_5
    · exact s36_3_6
    · exact s36_3_7
  · fin_cases v
    · exact s36_4_0
    · exact s36_4_1
    · exact s36_4_2
    · exact s36_4_3
    · exact s36_4_4
    · exact s36_4_5
    · exact s36_4_6
    · exact s36_4_7
  · fin_cases v
    · exact s36_5_0
    · exact s36_5_1
    · exact s36_5_2
    · exact s36_5_3
    · exact s36_5_4
    · exact s36_5_5
    · exact s36_5_6
    · exact s36_5_7
  · fin_cases v
    · exact s36_6_0
    · exact s36_6_1
    · exact s36_6_2
    · exact s36_6_3
    · exact s36_6_4
    · exact s36_6_5
    · exact s36_6_6
    · exact s36_6_7
  · exact List.all_eq_true.mp col36_7 v (List.mem_finRange v)
theorem col37_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 0 v) = true := by decide +kernel
theorem col37_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 1 v) = true := by decide +kernel
theorem col37_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 2 v) = true := by decide +kernel
theorem s37_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 0 = true := by decide +kernel
theorem s37_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 1 = true := by decide +kernel
theorem s37_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 2 = true := by decide +kernel
theorem s37_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 3 = true := by decide +kernel
theorem s37_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 4 = true := by decide +kernel
theorem s37_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 5 = true := by decide +kernel
theorem k37_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k37_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k37_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k37_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k37_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k37_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k37_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k37_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k37_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k37_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k37_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s37_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k37_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k37_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k37_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k37_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k37_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k37_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k37_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k37_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k37_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k37_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 3 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k37_3_6_130 k h.1 (by omega)
theorem s37_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 3 7 = true := by decide +kernel
theorem s37_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 0 = true := by decide +kernel
theorem s37_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 1 = true := by decide +kernel
theorem s37_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 2 = true := by decide +kernel
theorem s37_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 3 = true := by decide +kernel
theorem s37_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 4 = true := by decide +kernel
theorem s37_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 5 = true := by decide +kernel
theorem k37_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k37_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k37_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k37_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k37_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k37_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k37_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s37_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k37_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k37_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k37_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k37_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k37_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k37_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 4 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k37_4_6_126 k h.1 (by omega)
theorem s37_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 4 7 = true := by decide +kernel
theorem s37_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 0 = true := by decide +kernel
theorem s37_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 1 = true := by decide +kernel
theorem s37_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 2 = true := by decide +kernel
theorem s37_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 3 = true := by decide +kernel
theorem s37_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 4 = true := by decide +kernel
theorem s37_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 5 = true := by decide +kernel
theorem k37_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k37_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k37_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k37_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k37_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k37_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k37_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s37_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k37_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k37_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k37_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k37_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k37_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k37_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 5 6).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k37_5_6_126 k h.1 (by omega)
theorem s37_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 5 7 = true := by decide +kernel
theorem s37_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 0 = true := by decide +kernel
theorem s37_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 1 = true := by decide +kernel
theorem s37_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 2 = true := by decide +kernel
theorem s37_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 3 = true := by decide +kernel
theorem s37_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 4 = true := by decide +kernel
theorem s37_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 5 = true := by decide +kernel
theorem s37_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 6 = true := by decide +kernel
theorem k37_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k37_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k37_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k37_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k37_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s37_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k37_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k37_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k37_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k37_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 37) ((InDA1.TCasaD 3 6 7).getD (37 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k37_6_7_12 k h.1 (by omega)
theorem col37_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 7 v) = true := by decide +kernel
theorem col37 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 37) 37 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col37_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col37_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col37_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s37_3_0
    · exact s37_3_1
    · exact s37_3_2
    · exact s37_3_3
    · exact s37_3_4
    · exact s37_3_5
    · exact s37_3_6
    · exact s37_3_7
  · fin_cases v
    · exact s37_4_0
    · exact s37_4_1
    · exact s37_4_2
    · exact s37_4_3
    · exact s37_4_4
    · exact s37_4_5
    · exact s37_4_6
    · exact s37_4_7
  · fin_cases v
    · exact s37_5_0
    · exact s37_5_1
    · exact s37_5_2
    · exact s37_5_3
    · exact s37_5_4
    · exact s37_5_5
    · exact s37_5_6
    · exact s37_5_7
  · fin_cases v
    · exact s37_6_0
    · exact s37_6_1
    · exact s37_6_2
    · exact s37_6_3
    · exact s37_6_4
    · exact s37_6_5
    · exact s37_6_6
    · exact s37_6_7
  · exact List.all_eq_true.mp col37_7 v (List.mem_finRange v)
theorem col38_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 0 v) = true := by decide +kernel
theorem col38_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 1 v) = true := by decide +kernel
theorem col38_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 2 v) = true := by decide +kernel
theorem s38_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 0 = true := by decide +kernel
theorem s38_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 1 = true := by decide +kernel
theorem s38_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 2 = true := by decide +kernel
theorem k38_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k38_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k38_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s38_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k38_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k38_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 38) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (38 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k38_3_3_26 k h.1 (by omega)
theorem s38_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 4 = true := by decide +kernel
theorem s38_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 5 = true := by decide +kernel
theorem k38_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k38_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k38_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k38_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k38_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k38_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k38_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k38_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k38_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k38_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k38_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s38_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k38_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k38_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k38_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k38_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k38_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k38_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k38_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k38_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k38_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k38_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TTsaaD 3 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k38_3_6_130 k h.1 (by omega)
theorem s38_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 3 7 = true := by decide +kernel
theorem s38_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 0 = true := by decide +kernel
theorem s38_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 1 = true := by decide +kernel
theorem s38_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 2 = true := by decide +kernel
theorem s38_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 3 = true := by decide +kernel
theorem s38_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 4 = true := by decide +kernel
theorem s38_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 5 = true := by decide +kernel
theorem k38_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k38_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k38_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k38_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k38_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k38_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k38_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s38_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k38_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k38_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k38_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k38_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k38_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k38_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 4 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k38_4_6_126 k h.1 (by omega)
theorem s38_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 4 7 = true := by decide +kernel
theorem s38_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 0 = true := by decide +kernel
theorem s38_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 1 = true := by decide +kernel
theorem s38_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 2 = true := by decide +kernel
theorem s38_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 3 = true := by decide +kernel
theorem s38_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 4 = true := by decide +kernel
theorem s38_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 5 = true := by decide +kernel
theorem k38_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k38_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k38_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k38_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k38_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k38_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k38_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s38_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k38_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k38_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k38_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k38_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k38_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k38_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 5 6).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k38_5_6_126 k h.1 (by omega)
theorem s38_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 5 7 = true := by decide +kernel
theorem s38_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 0 = true := by decide +kernel
theorem s38_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 1 = true := by decide +kernel
theorem s38_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 2 = true := by decide +kernel
theorem s38_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 3 = true := by decide +kernel
theorem s38_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 4 = true := by decide +kernel
theorem s38_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 5 = true := by decide +kernel
theorem s38_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 6 = true := by decide +kernel
theorem k38_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k38_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k38_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k38_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k38_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s38_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k38_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k38_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k38_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k38_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 38) ((InDA1.TCasaD 4 6 7).getD (38 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k38_6_7_12 k h.1 (by omega)
theorem col38_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 7 v) = true := by decide +kernel
theorem col38 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 38) 38 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col38_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col38_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col38_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s38_3_0
    · exact s38_3_1
    · exact s38_3_2
    · exact s38_3_3
    · exact s38_3_4
    · exact s38_3_5
    · exact s38_3_6
    · exact s38_3_7
  · fin_cases v
    · exact s38_4_0
    · exact s38_4_1
    · exact s38_4_2
    · exact s38_4_3
    · exact s38_4_4
    · exact s38_4_5
    · exact s38_4_6
    · exact s38_4_7
  · fin_cases v
    · exact s38_5_0
    · exact s38_5_1
    · exact s38_5_2
    · exact s38_5_3
    · exact s38_5_4
    · exact s38_5_5
    · exact s38_5_6
    · exact s38_5_7
  · fin_cases v
    · exact s38_6_0
    · exact s38_6_1
    · exact s38_6_2
    · exact s38_6_3
    · exact s38_6_4
    · exact s38_6_5
    · exact s38_6_6
    · exact s38_6_7
  · exact List.all_eq_true.mp col38_7 v (List.mem_finRange v)
theorem col39_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 0 v) = true := by decide +kernel
theorem col39_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 1 v) = true := by decide +kernel
theorem col39_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 2 v) = true := by decide +kernel
theorem s39_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 0 = true := by decide +kernel
theorem s39_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 1 = true := by decide +kernel
theorem s39_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 2 = true := by decide +kernel
theorem k39_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k39_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k39_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s39_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k39_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k39_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 39) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (39 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k39_3_3_26 k h.1 (by omega)
theorem s39_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 4 = true := by decide +kernel
theorem s39_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 5 = true := by decide +kernel
theorem k39_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k39_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k39_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k39_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k39_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k39_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k39_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k39_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k39_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k39_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k39_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s39_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k39_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k39_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k39_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k39_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k39_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k39_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k39_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k39_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k39_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k39_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TTsaaD 3 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k39_3_6_130 k h.1 (by omega)
theorem s39_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 3 7 = true := by decide +kernel
theorem s39_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 0 = true := by decide +kernel
theorem s39_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 1 = true := by decide +kernel
theorem s39_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 2 = true := by decide +kernel
theorem s39_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 3 = true := by decide +kernel
theorem s39_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 4 = true := by decide +kernel
theorem s39_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 5 = true := by decide +kernel
theorem k39_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k39_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k39_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k39_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k39_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k39_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k39_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s39_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k39_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k39_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k39_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k39_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k39_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k39_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 4 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k39_4_6_126 k h.1 (by omega)
theorem s39_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 4 7 = true := by decide +kernel
theorem s39_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 0 = true := by decide +kernel
theorem s39_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 1 = true := by decide +kernel
theorem s39_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 2 = true := by decide +kernel
theorem s39_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 3 = true := by decide +kernel
theorem s39_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 4 = true := by decide +kernel
theorem s39_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 5 = true := by decide +kernel
theorem k39_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k39_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k39_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k39_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k39_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k39_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k39_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s39_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k39_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k39_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k39_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k39_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k39_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k39_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 5 6).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k39_5_6_126 k h.1 (by omega)
theorem s39_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 5 7 = true := by decide +kernel
theorem s39_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 0 = true := by decide +kernel
theorem s39_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 1 = true := by decide +kernel
theorem s39_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 2 = true := by decide +kernel
theorem s39_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 3 = true := by decide +kernel
theorem s39_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 4 = true := by decide +kernel
theorem s39_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 5 = true := by decide +kernel
theorem s39_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 6 = true := by decide +kernel
theorem k39_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k39_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k39_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k39_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k39_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s39_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k39_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k39_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k39_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k39_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 39) ((InDA1.TCasaD 4 6 7).getD (39 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k39_6_7_12 k h.1 (by omega)
theorem col39_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 7 v) = true := by decide +kernel
theorem col39 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 39) 39 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col39_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col39_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col39_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s39_3_0
    · exact s39_3_1
    · exact s39_3_2
    · exact s39_3_3
    · exact s39_3_4
    · exact s39_3_5
    · exact s39_3_6
    · exact s39_3_7
  · fin_cases v
    · exact s39_4_0
    · exact s39_4_1
    · exact s39_4_2
    · exact s39_4_3
    · exact s39_4_4
    · exact s39_4_5
    · exact s39_4_6
    · exact s39_4_7
  · fin_cases v
    · exact s39_5_0
    · exact s39_5_1
    · exact s39_5_2
    · exact s39_5_3
    · exact s39_5_4
    · exact s39_5_5
    · exact s39_5_6
    · exact s39_5_7
  · fin_cases v
    · exact s39_6_0
    · exact s39_6_1
    · exact s39_6_2
    · exact s39_6_3
    · exact s39_6_4
    · exact s39_6_5
    · exact s39_6_6
    · exact s39_6_7
  · exact List.all_eq_true.mp col39_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
