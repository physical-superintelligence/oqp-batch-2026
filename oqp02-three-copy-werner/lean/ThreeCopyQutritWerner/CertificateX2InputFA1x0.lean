module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [0, 5). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col0_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 0 v) = true := by decide +kernel
theorem col0_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 1 v) = true := by decide +kernel
theorem col0_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 2 v) = true := by decide +kernel
theorem s0_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 0 = true := by decide +kernel
theorem s0_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 1 = true := by decide +kernel
theorem s0_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 2 = true := by decide +kernel
theorem s0_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 3 = true := by decide +kernel
theorem s0_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 4 = true := by decide +kernel
theorem s0_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 5 = true := by decide +kernel
theorem k0_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k0_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k0_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k0_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k0_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k0_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k0_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k0_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k0_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k0_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k0_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s0_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k0_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k0_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k0_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k0_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k0_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k0_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k0_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k0_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k0_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k0_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 3 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k0_3_6_130 k h.1 (by omega)
theorem s0_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 3 7 = true := by decide +kernel
theorem s0_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 0 = true := by decide +kernel
theorem s0_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 1 = true := by decide +kernel
theorem s0_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 2 = true := by decide +kernel
theorem s0_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 3 = true := by decide +kernel
theorem s0_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 4 = true := by decide +kernel
theorem s0_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 5 = true := by decide +kernel
theorem k0_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k0_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k0_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k0_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k0_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k0_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k0_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s0_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k0_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k0_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k0_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k0_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k0_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k0_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 4 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k0_4_6_126 k h.1 (by omega)
theorem s0_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 4 7 = true := by decide +kernel
theorem s0_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 0 = true := by decide +kernel
theorem s0_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 1 = true := by decide +kernel
theorem s0_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 2 = true := by decide +kernel
theorem s0_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 3 = true := by decide +kernel
theorem s0_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 4 = true := by decide +kernel
theorem s0_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 5 = true := by decide +kernel
theorem k0_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k0_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k0_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k0_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k0_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k0_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k0_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s0_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k0_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k0_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k0_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k0_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k0_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k0_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 5 6).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k0_5_6_126 k h.1 (by omega)
theorem s0_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 5 7 = true := by decide +kernel
theorem s0_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 0 = true := by decide +kernel
theorem s0_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 1 = true := by decide +kernel
theorem s0_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 2 = true := by decide +kernel
theorem s0_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 3 = true := by decide +kernel
theorem s0_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 4 = true := by decide +kernel
theorem s0_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 5 = true := by decide +kernel
theorem s0_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 6 = true := by decide +kernel
theorem k0_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k0_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k0_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k0_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k0_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s0_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 6 7 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k0_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k0_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k0_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k0_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 0) ((InDA1.TCasaD 1 6 7).getD (0 - x2AOff 1 1) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k0_6_7_12 k h.1 (by omega)
theorem col0_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 7 v) = true := by decide +kernel
theorem col0 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 0) 0 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col0_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col0_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col0_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s0_3_0
    · exact s0_3_1
    · exact s0_3_2
    · exact s0_3_3
    · exact s0_3_4
    · exact s0_3_5
    · exact s0_3_6
    · exact s0_3_7
  · fin_cases v
    · exact s0_4_0
    · exact s0_4_1
    · exact s0_4_2
    · exact s0_4_3
    · exact s0_4_4
    · exact s0_4_5
    · exact s0_4_6
    · exact s0_4_7
  · fin_cases v
    · exact s0_5_0
    · exact s0_5_1
    · exact s0_5_2
    · exact s0_5_3
    · exact s0_5_4
    · exact s0_5_5
    · exact s0_5_6
    · exact s0_5_7
  · fin_cases v
    · exact s0_6_0
    · exact s0_6_1
    · exact s0_6_2
    · exact s0_6_3
    · exact s0_6_4
    · exact s0_6_5
    · exact s0_6_6
    · exact s0_6_7
  · exact List.all_eq_true.mp col0_7 v (List.mem_finRange v)
theorem col1_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 0 v) = true := by decide +kernel
theorem col1_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 1 v) = true := by decide +kernel
theorem col1_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 2 v) = true := by decide +kernel
theorem s1_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 0 = true := by decide +kernel
theorem s1_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 1 = true := by decide +kernel
theorem s1_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 2 = true := by decide +kernel
theorem s1_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 3 = true := by decide +kernel
theorem s1_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 4 = true := by decide +kernel
theorem s1_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 5 = true := by decide +kernel
theorem k1_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k1_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k1_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k1_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k1_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k1_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k1_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k1_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k1_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k1_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k1_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s1_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k1_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k1_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k1_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k1_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k1_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k1_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k1_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k1_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k1_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k1_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 3 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k1_3_6_130 k h.1 (by omega)
theorem s1_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 3 7 = true := by decide +kernel
theorem s1_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 0 = true := by decide +kernel
theorem s1_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 1 = true := by decide +kernel
theorem s1_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 2 = true := by decide +kernel
theorem s1_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 3 = true := by decide +kernel
theorem s1_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 4 = true := by decide +kernel
theorem s1_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 5 = true := by decide +kernel
theorem k1_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k1_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k1_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k1_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k1_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k1_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k1_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s1_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k1_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k1_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k1_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k1_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k1_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k1_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 4 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k1_4_6_126 k h.1 (by omega)
theorem s1_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 4 7 = true := by decide +kernel
theorem s1_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 0 = true := by decide +kernel
theorem s1_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 1 = true := by decide +kernel
theorem s1_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 2 = true := by decide +kernel
theorem s1_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 3 = true := by decide +kernel
theorem s1_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 4 = true := by decide +kernel
theorem s1_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 5 = true := by decide +kernel
theorem k1_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k1_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k1_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k1_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k1_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k1_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k1_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s1_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k1_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k1_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k1_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k1_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k1_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k1_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 5 6).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k1_5_6_126 k h.1 (by omega)
theorem s1_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 5 7 = true := by decide +kernel
theorem s1_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 0 = true := by decide +kernel
theorem s1_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 1 = true := by decide +kernel
theorem s1_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 2 = true := by decide +kernel
theorem s1_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 3 = true := by decide +kernel
theorem s1_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 4 = true := by decide +kernel
theorem s1_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 5 = true := by decide +kernel
theorem s1_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 6 = true := by decide +kernel
theorem k1_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k1_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k1_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k1_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k1_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s1_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 6 7 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k1_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k1_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k1_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k1_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 1) ((InDA1.TCasaD 2 6 7).getD (1 - x2AOff 1 2) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k1_6_7_12 k h.1 (by omega)
theorem col1_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 7 v) = true := by decide +kernel
theorem col1 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 1) 1 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col1_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col1_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col1_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s1_3_0
    · exact s1_3_1
    · exact s1_3_2
    · exact s1_3_3
    · exact s1_3_4
    · exact s1_3_5
    · exact s1_3_6
    · exact s1_3_7
  · fin_cases v
    · exact s1_4_0
    · exact s1_4_1
    · exact s1_4_2
    · exact s1_4_3
    · exact s1_4_4
    · exact s1_4_5
    · exact s1_4_6
    · exact s1_4_7
  · fin_cases v
    · exact s1_5_0
    · exact s1_5_1
    · exact s1_5_2
    · exact s1_5_3
    · exact s1_5_4
    · exact s1_5_5
    · exact s1_5_6
    · exact s1_5_7
  · fin_cases v
    · exact s1_6_0
    · exact s1_6_1
    · exact s1_6_2
    · exact s1_6_3
    · exact s1_6_4
    · exact s1_6_5
    · exact s1_6_6
    · exact s1_6_7
  · exact List.all_eq_true.mp col1_7 v (List.mem_finRange v)
theorem col2_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 0 v) = true := by decide +kernel
theorem col2_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 1 v) = true := by decide +kernel
theorem col2_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 2 v) = true := by decide +kernel
theorem s2_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 0 = true := by decide +kernel
theorem s2_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 1 = true := by decide +kernel
theorem s2_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 2 = true := by decide +kernel
theorem s2_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 3 = true := by decide +kernel
theorem s2_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 4 = true := by decide +kernel
theorem s2_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 5 = true := by decide +kernel
theorem k2_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k2_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k2_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k2_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k2_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k2_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k2_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k2_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k2_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k2_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k2_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s2_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k2_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k2_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k2_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k2_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k2_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k2_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k2_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k2_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k2_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k2_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 3 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k2_3_6_130 k h.1 (by omega)
theorem s2_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 3 7 = true := by decide +kernel
theorem s2_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 0 = true := by decide +kernel
theorem s2_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 1 = true := by decide +kernel
theorem s2_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 2 = true := by decide +kernel
theorem s2_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 3 = true := by decide +kernel
theorem s2_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 4 = true := by decide +kernel
theorem s2_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 5 = true := by decide +kernel
theorem k2_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k2_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k2_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k2_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k2_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k2_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k2_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s2_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k2_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k2_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k2_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k2_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k2_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k2_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 4 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k2_4_6_126 k h.1 (by omega)
theorem s2_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 4 7 = true := by decide +kernel
theorem s2_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 0 = true := by decide +kernel
theorem s2_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 1 = true := by decide +kernel
theorem s2_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 2 = true := by decide +kernel
theorem s2_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 3 = true := by decide +kernel
theorem s2_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 4 = true := by decide +kernel
theorem s2_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 5 = true := by decide +kernel
theorem k2_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k2_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k2_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k2_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k2_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k2_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k2_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s2_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k2_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k2_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k2_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k2_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k2_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k2_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 5 6).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k2_5_6_126 k h.1 (by omega)
theorem s2_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 5 7 = true := by decide +kernel
theorem s2_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 0 = true := by decide +kernel
theorem s2_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 1 = true := by decide +kernel
theorem s2_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 2 = true := by decide +kernel
theorem s2_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 3 = true := by decide +kernel
theorem s2_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 4 = true := by decide +kernel
theorem s2_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 5 = true := by decide +kernel
theorem s2_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 6 = true := by decide +kernel
theorem k2_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k2_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k2_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k2_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k2_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s2_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k2_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k2_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k2_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k2_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 2) ((InDA1.TCasaD 3 6 7).getD (2 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k2_6_7_12 k h.1 (by omega)
theorem col2_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 7 v) = true := by decide +kernel
theorem col2 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 2) 2 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col2_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col2_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col2_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s2_3_0
    · exact s2_3_1
    · exact s2_3_2
    · exact s2_3_3
    · exact s2_3_4
    · exact s2_3_5
    · exact s2_3_6
    · exact s2_3_7
  · fin_cases v
    · exact s2_4_0
    · exact s2_4_1
    · exact s2_4_2
    · exact s2_4_3
    · exact s2_4_4
    · exact s2_4_5
    · exact s2_4_6
    · exact s2_4_7
  · fin_cases v
    · exact s2_5_0
    · exact s2_5_1
    · exact s2_5_2
    · exact s2_5_3
    · exact s2_5_4
    · exact s2_5_5
    · exact s2_5_6
    · exact s2_5_7
  · fin_cases v
    · exact s2_6_0
    · exact s2_6_1
    · exact s2_6_2
    · exact s2_6_3
    · exact s2_6_4
    · exact s2_6_5
    · exact s2_6_6
    · exact s2_6_7
  · exact List.all_eq_true.mp col2_7 v (List.mem_finRange v)
theorem col3_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 0 v) = true := by decide +kernel
theorem col3_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 1 v) = true := by decide +kernel
theorem col3_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 2 v) = true := by decide +kernel
theorem s3_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 0 = true := by decide +kernel
theorem s3_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 1 = true := by decide +kernel
theorem s3_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 2 = true := by decide +kernel
theorem s3_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 3 = true := by decide +kernel
theorem s3_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 4 = true := by decide +kernel
theorem s3_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 5 = true := by decide +kernel
theorem k3_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k3_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k3_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k3_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k3_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k3_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k3_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k3_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k3_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k3_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k3_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s3_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k3_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k3_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k3_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k3_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k3_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k3_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k3_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k3_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k3_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k3_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 3 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k3_3_6_130 k h.1 (by omega)
theorem s3_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 3 7 = true := by decide +kernel
theorem s3_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 0 = true := by decide +kernel
theorem s3_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 1 = true := by decide +kernel
theorem s3_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 2 = true := by decide +kernel
theorem s3_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 3 = true := by decide +kernel
theorem s3_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 4 = true := by decide +kernel
theorem s3_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 5 = true := by decide +kernel
theorem k3_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k3_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k3_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k3_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k3_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k3_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k3_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s3_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k3_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k3_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k3_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k3_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k3_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k3_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 4 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k3_4_6_126 k h.1 (by omega)
theorem s3_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 4 7 = true := by decide +kernel
theorem s3_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 0 = true := by decide +kernel
theorem s3_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 1 = true := by decide +kernel
theorem s3_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 2 = true := by decide +kernel
theorem s3_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 3 = true := by decide +kernel
theorem s3_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 4 = true := by decide +kernel
theorem s3_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 5 = true := by decide +kernel
theorem k3_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k3_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k3_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k3_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k3_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k3_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k3_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s3_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k3_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k3_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k3_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k3_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k3_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k3_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 5 6).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k3_5_6_126 k h.1 (by omega)
theorem s3_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 5 7 = true := by decide +kernel
theorem s3_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 0 = true := by decide +kernel
theorem s3_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 1 = true := by decide +kernel
theorem s3_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 2 = true := by decide +kernel
theorem s3_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 3 = true := by decide +kernel
theorem s3_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 4 = true := by decide +kernel
theorem s3_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 5 = true := by decide +kernel
theorem s3_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 6 = true := by decide +kernel
theorem k3_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k3_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k3_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k3_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k3_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s3_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k3_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k3_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k3_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k3_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 3) ((InDA1.TCasaD 3 6 7).getD (3 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k3_6_7_12 k h.1 (by omega)
theorem col3_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 7 v) = true := by decide +kernel
theorem col3 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 3) 3 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col3_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col3_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col3_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s3_3_0
    · exact s3_3_1
    · exact s3_3_2
    · exact s3_3_3
    · exact s3_3_4
    · exact s3_3_5
    · exact s3_3_6
    · exact s3_3_7
  · fin_cases v
    · exact s3_4_0
    · exact s3_4_1
    · exact s3_4_2
    · exact s3_4_3
    · exact s3_4_4
    · exact s3_4_5
    · exact s3_4_6
    · exact s3_4_7
  · fin_cases v
    · exact s3_5_0
    · exact s3_5_1
    · exact s3_5_2
    · exact s3_5_3
    · exact s3_5_4
    · exact s3_5_5
    · exact s3_5_6
    · exact s3_5_7
  · fin_cases v
    · exact s3_6_0
    · exact s3_6_1
    · exact s3_6_2
    · exact s3_6_3
    · exact s3_6_4
    · exact s3_6_5
    · exact s3_6_6
    · exact s3_6_7
  · exact List.all_eq_true.mp col3_7 v (List.mem_finRange v)
theorem col4_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 0 v) = true := by decide +kernel
theorem col4_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 1 v) = true := by decide +kernel
theorem col4_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 2 v) = true := by decide +kernel
theorem s4_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 0 = true := by decide +kernel
theorem s4_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 1 = true := by decide +kernel
theorem s4_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 2 = true := by decide +kernel
theorem s4_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 3 = true := by decide +kernel
theorem s4_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 4 = true := by decide +kernel
theorem s4_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 5 = true := by decide +kernel
theorem k4_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k4_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k4_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k4_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k4_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k4_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k4_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k4_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k4_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k4_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k4_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s4_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k4_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k4_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k4_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k4_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k4_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k4_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k4_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k4_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k4_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k4_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 3 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k4_3_6_130 k h.1 (by omega)
theorem s4_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 3 7 = true := by decide +kernel
theorem s4_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 0 = true := by decide +kernel
theorem s4_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 1 = true := by decide +kernel
theorem s4_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 2 = true := by decide +kernel
theorem s4_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 3 = true := by decide +kernel
theorem s4_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 4 = true := by decide +kernel
theorem s4_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 5 = true := by decide +kernel
theorem k4_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k4_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k4_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k4_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k4_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k4_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k4_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s4_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k4_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k4_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k4_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k4_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k4_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k4_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 4 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k4_4_6_126 k h.1 (by omega)
theorem s4_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 4 7 = true := by decide +kernel
theorem s4_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 0 = true := by decide +kernel
theorem s4_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 1 = true := by decide +kernel
theorem s4_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 2 = true := by decide +kernel
theorem s4_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 3 = true := by decide +kernel
theorem s4_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 4 = true := by decide +kernel
theorem s4_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 5 = true := by decide +kernel
theorem k4_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k4_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k4_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k4_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k4_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k4_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k4_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s4_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k4_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k4_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k4_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k4_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k4_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k4_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 5 6).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k4_5_6_126 k h.1 (by omega)
theorem s4_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 5 7 = true := by decide +kernel
theorem s4_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 0 = true := by decide +kernel
theorem s4_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 1 = true := by decide +kernel
theorem s4_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 2 = true := by decide +kernel
theorem s4_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 3 = true := by decide +kernel
theorem s4_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 4 = true := by decide +kernel
theorem s4_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 5 = true := by decide +kernel
theorem s4_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 6 = true := by decide +kernel
theorem k4_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k4_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k4_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k4_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k4_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s4_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 6 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k4_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k4_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k4_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k4_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 4) ((InDA1.TCasaD 3 6 7).getD (4 - x2AOff 1 3) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k4_6_7_12 k h.1 (by omega)
theorem col4_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 7 v) = true := by decide +kernel
theorem col4 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 4) 4 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col4_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col4_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col4_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s4_3_0
    · exact s4_3_1
    · exact s4_3_2
    · exact s4_3_3
    · exact s4_3_4
    · exact s4_3_5
    · exact s4_3_6
    · exact s4_3_7
  · fin_cases v
    · exact s4_4_0
    · exact s4_4_1
    · exact s4_4_2
    · exact s4_4_3
    · exact s4_4_4
    · exact s4_4_5
    · exact s4_4_6
    · exact s4_4_7
  · fin_cases v
    · exact s4_5_0
    · exact s4_5_1
    · exact s4_5_2
    · exact s4_5_3
    · exact s4_5_4
    · exact s4_5_5
    · exact s4_5_6
    · exact s4_5_7
  · fin_cases v
    · exact s4_6_0
    · exact s4_6_1
    · exact s4_6_2
    · exact s4_6_3
    · exact s4_6_4
    · exact s4_6_5
    · exact s4_6_6
    · exact s4_6_7
  · exact List.all_eq_true.mp col4_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
