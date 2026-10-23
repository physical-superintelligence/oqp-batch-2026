module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [75, 80). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col75_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 0 v) = true := by decide +kernel
theorem col75_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 1 v) = true := by decide +kernel
theorem col75_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 2 v) = true := by decide +kernel
theorem s75_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 0 = true := by decide +kernel
theorem s75_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 1 = true := by decide +kernel
theorem s75_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 2 = true := by decide +kernel
theorem k75_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k75_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k75_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s75_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k75_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k75_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 75) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (75 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k75_3_3_26 k h.1 (by omega)
theorem s75_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 4 = true := by decide +kernel
theorem s75_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 5 = true := by decide +kernel
theorem k75_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k75_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k75_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k75_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k75_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k75_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k75_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k75_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k75_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k75_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k75_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s75_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k75_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k75_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k75_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k75_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k75_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k75_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k75_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k75_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k75_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k75_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 3 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k75_3_6_130 k h.1 (by omega)
theorem s75_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 3 7 = true := by decide +kernel
theorem s75_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 0 = true := by decide +kernel
theorem s75_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 1 = true := by decide +kernel
theorem s75_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 2 = true := by decide +kernel
theorem s75_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 3 = true := by decide +kernel
theorem s75_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 4 = true := by decide +kernel
theorem s75_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 5 = true := by decide +kernel
theorem k75_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k75_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k75_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k75_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k75_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k75_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k75_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s75_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k75_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k75_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k75_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k75_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k75_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k75_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TTsaaD 4 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k75_4_6_126 k h.1 (by omega)
theorem s75_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 4 7 = true := by decide +kernel
theorem s75_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 0 = true := by decide +kernel
theorem s75_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 1 = true := by decide +kernel
theorem s75_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 2 = true := by decide +kernel
theorem s75_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 3 = true := by decide +kernel
theorem s75_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 4 = true := by decide +kernel
theorem s75_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 5 = true := by decide +kernel
theorem k75_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k75_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k75_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k75_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k75_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k75_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k75_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s75_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k75_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k75_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k75_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k75_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k75_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k75_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 5 6).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k75_5_6_126 k h.1 (by omega)
theorem s75_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 5 7 = true := by decide +kernel
theorem s75_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 0 = true := by decide +kernel
theorem s75_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 1 = true := by decide +kernel
theorem s75_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 2 = true := by decide +kernel
theorem s75_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 3 = true := by decide +kernel
theorem s75_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 4 = true := by decide +kernel
theorem s75_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 5 = true := by decide +kernel
theorem s75_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 6 = true := by decide +kernel
theorem k75_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k75_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k75_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k75_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k75_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s75_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k75_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k75_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k75_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k75_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 75) ((InDA1.TCasaD 5 6 7).getD (75 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k75_6_7_12 k h.1 (by omega)
theorem col75_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 7 v) = true := by decide +kernel
theorem col75 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 75) 75 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col75_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col75_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col75_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s75_3_0
    · exact s75_3_1
    · exact s75_3_2
    · exact s75_3_3
    · exact s75_3_4
    · exact s75_3_5
    · exact s75_3_6
    · exact s75_3_7
  · fin_cases v
    · exact s75_4_0
    · exact s75_4_1
    · exact s75_4_2
    · exact s75_4_3
    · exact s75_4_4
    · exact s75_4_5
    · exact s75_4_6
    · exact s75_4_7
  · fin_cases v
    · exact s75_5_0
    · exact s75_5_1
    · exact s75_5_2
    · exact s75_5_3
    · exact s75_5_4
    · exact s75_5_5
    · exact s75_5_6
    · exact s75_5_7
  · fin_cases v
    · exact s75_6_0
    · exact s75_6_1
    · exact s75_6_2
    · exact s75_6_3
    · exact s75_6_4
    · exact s75_6_5
    · exact s75_6_6
    · exact s75_6_7
  · exact List.all_eq_true.mp col75_7 v (List.mem_finRange v)
theorem col76_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 0 v) = true := by decide +kernel
theorem col76_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 1 v) = true := by decide +kernel
theorem col76_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 2 v) = true := by decide +kernel
theorem s76_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 0 = true := by decide +kernel
theorem s76_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 1 = true := by decide +kernel
theorem s76_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 2 = true := by decide +kernel
theorem k76_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k76_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k76_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s76_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k76_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k76_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 76) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (76 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k76_3_3_26 k h.1 (by omega)
theorem s76_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 4 = true := by decide +kernel
theorem s76_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 5 = true := by decide +kernel
theorem k76_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k76_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k76_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k76_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k76_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k76_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k76_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k76_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k76_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k76_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k76_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s76_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k76_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k76_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k76_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k76_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k76_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k76_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k76_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k76_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k76_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k76_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 3 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k76_3_6_130 k h.1 (by omega)
theorem s76_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 3 7 = true := by decide +kernel
theorem s76_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 0 = true := by decide +kernel
theorem s76_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 1 = true := by decide +kernel
theorem s76_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 2 = true := by decide +kernel
theorem s76_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 3 = true := by decide +kernel
theorem s76_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 4 = true := by decide +kernel
theorem s76_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 5 = true := by decide +kernel
theorem k76_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k76_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k76_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k76_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k76_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k76_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k76_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s76_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k76_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k76_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k76_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k76_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k76_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k76_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TTsaaD 4 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k76_4_6_126 k h.1 (by omega)
theorem s76_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 4 7 = true := by decide +kernel
theorem s76_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 0 = true := by decide +kernel
theorem s76_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 1 = true := by decide +kernel
theorem s76_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 2 = true := by decide +kernel
theorem s76_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 3 = true := by decide +kernel
theorem s76_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 4 = true := by decide +kernel
theorem s76_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 5 = true := by decide +kernel
theorem k76_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k76_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k76_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k76_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k76_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k76_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k76_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s76_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k76_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k76_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k76_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k76_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k76_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k76_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 5 6).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k76_5_6_126 k h.1 (by omega)
theorem s76_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 5 7 = true := by decide +kernel
theorem s76_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 0 = true := by decide +kernel
theorem s76_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 1 = true := by decide +kernel
theorem s76_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 2 = true := by decide +kernel
theorem s76_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 3 = true := by decide +kernel
theorem s76_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 4 = true := by decide +kernel
theorem s76_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 5 = true := by decide +kernel
theorem s76_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 6 = true := by decide +kernel
theorem k76_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k76_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k76_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k76_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k76_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s76_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k76_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k76_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k76_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k76_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 76) ((InDA1.TCasaD 5 6 7).getD (76 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k76_6_7_12 k h.1 (by omega)
theorem col76_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 7 v) = true := by decide +kernel
theorem col76 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 76) 76 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col76_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col76_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col76_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s76_3_0
    · exact s76_3_1
    · exact s76_3_2
    · exact s76_3_3
    · exact s76_3_4
    · exact s76_3_5
    · exact s76_3_6
    · exact s76_3_7
  · fin_cases v
    · exact s76_4_0
    · exact s76_4_1
    · exact s76_4_2
    · exact s76_4_3
    · exact s76_4_4
    · exact s76_4_5
    · exact s76_4_6
    · exact s76_4_7
  · fin_cases v
    · exact s76_5_0
    · exact s76_5_1
    · exact s76_5_2
    · exact s76_5_3
    · exact s76_5_4
    · exact s76_5_5
    · exact s76_5_6
    · exact s76_5_7
  · fin_cases v
    · exact s76_6_0
    · exact s76_6_1
    · exact s76_6_2
    · exact s76_6_3
    · exact s76_6_4
    · exact s76_6_5
    · exact s76_6_6
    · exact s76_6_7
  · exact List.all_eq_true.mp col76_7 v (List.mem_finRange v)
theorem col77_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 0 v) = true := by decide +kernel
theorem col77_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 1 v) = true := by decide +kernel
theorem col77_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 2 v) = true := by decide +kernel
theorem s77_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 0 = true := by decide +kernel
theorem s77_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 1 = true := by decide +kernel
theorem s77_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 2 = true := by decide +kernel
theorem k77_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k77_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k77_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s77_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k77_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k77_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 77) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (77 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k77_3_3_26 k h.1 (by omega)
theorem s77_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 4 = true := by decide +kernel
theorem s77_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 5 = true := by decide +kernel
theorem k77_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k77_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k77_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k77_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k77_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k77_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k77_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k77_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k77_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k77_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k77_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s77_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k77_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k77_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k77_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k77_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k77_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k77_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k77_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k77_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k77_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k77_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 3 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k77_3_6_130 k h.1 (by omega)
theorem s77_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 3 7 = true := by decide +kernel
theorem s77_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 0 = true := by decide +kernel
theorem s77_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 1 = true := by decide +kernel
theorem s77_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 2 = true := by decide +kernel
theorem s77_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 3 = true := by decide +kernel
theorem s77_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 4 = true := by decide +kernel
theorem s77_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 5 = true := by decide +kernel
theorem k77_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k77_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k77_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k77_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k77_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k77_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k77_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s77_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k77_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k77_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k77_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k77_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k77_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k77_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TTsaaD 4 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k77_4_6_126 k h.1 (by omega)
theorem s77_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 4 7 = true := by decide +kernel
theorem s77_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 0 = true := by decide +kernel
theorem s77_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 1 = true := by decide +kernel
theorem s77_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 2 = true := by decide +kernel
theorem s77_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 3 = true := by decide +kernel
theorem s77_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 4 = true := by decide +kernel
theorem s77_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 5 = true := by decide +kernel
theorem k77_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k77_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k77_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k77_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k77_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k77_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k77_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s77_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k77_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k77_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k77_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k77_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k77_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k77_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 5 6).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k77_5_6_126 k h.1 (by omega)
theorem s77_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 5 7 = true := by decide +kernel
theorem s77_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 0 = true := by decide +kernel
theorem s77_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 1 = true := by decide +kernel
theorem s77_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 2 = true := by decide +kernel
theorem s77_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 3 = true := by decide +kernel
theorem s77_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 4 = true := by decide +kernel
theorem s77_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 5 = true := by decide +kernel
theorem s77_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 6 = true := by decide +kernel
theorem k77_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k77_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k77_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k77_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k77_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s77_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k77_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k77_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k77_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k77_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 77) ((InDA1.TCasaD 5 6 7).getD (77 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k77_6_7_12 k h.1 (by omega)
theorem col77_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 7 v) = true := by decide +kernel
theorem col77 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 77) 77 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col77_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col77_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col77_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s77_3_0
    · exact s77_3_1
    · exact s77_3_2
    · exact s77_3_3
    · exact s77_3_4
    · exact s77_3_5
    · exact s77_3_6
    · exact s77_3_7
  · fin_cases v
    · exact s77_4_0
    · exact s77_4_1
    · exact s77_4_2
    · exact s77_4_3
    · exact s77_4_4
    · exact s77_4_5
    · exact s77_4_6
    · exact s77_4_7
  · fin_cases v
    · exact s77_5_0
    · exact s77_5_1
    · exact s77_5_2
    · exact s77_5_3
    · exact s77_5_4
    · exact s77_5_5
    · exact s77_5_6
    · exact s77_5_7
  · fin_cases v
    · exact s77_6_0
    · exact s77_6_1
    · exact s77_6_2
    · exact s77_6_3
    · exact s77_6_4
    · exact s77_6_5
    · exact s77_6_6
    · exact s77_6_7
  · exact List.all_eq_true.mp col77_7 v (List.mem_finRange v)
theorem col78_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 0 v) = true := by decide +kernel
theorem col78_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 1 v) = true := by decide +kernel
theorem col78_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 2 v) = true := by decide +kernel
theorem s78_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 0 = true := by decide +kernel
theorem s78_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 1 = true := by decide +kernel
theorem s78_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 2 = true := by decide +kernel
theorem k78_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k78_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k78_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s78_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k78_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k78_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 78) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (78 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k78_3_3_26 k h.1 (by omega)
theorem s78_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 4 = true := by decide +kernel
theorem s78_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 5 = true := by decide +kernel
theorem k78_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k78_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k78_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k78_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k78_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k78_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k78_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k78_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k78_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k78_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k78_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s78_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k78_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k78_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k78_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k78_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k78_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k78_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k78_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k78_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k78_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k78_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 3 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k78_3_6_130 k h.1 (by omega)
theorem s78_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 3 7 = true := by decide +kernel
theorem s78_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 0 = true := by decide +kernel
theorem s78_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 1 = true := by decide +kernel
theorem s78_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 2 = true := by decide +kernel
theorem s78_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 3 = true := by decide +kernel
theorem s78_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 4 = true := by decide +kernel
theorem s78_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 5 = true := by decide +kernel
theorem k78_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k78_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k78_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k78_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k78_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k78_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k78_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s78_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k78_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k78_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k78_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k78_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k78_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k78_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TTsaaD 4 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k78_4_6_126 k h.1 (by omega)
theorem s78_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 4 7 = true := by decide +kernel
theorem s78_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 0 = true := by decide +kernel
theorem s78_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 1 = true := by decide +kernel
theorem s78_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 2 = true := by decide +kernel
theorem s78_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 3 = true := by decide +kernel
theorem s78_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 4 = true := by decide +kernel
theorem s78_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 5 = true := by decide +kernel
theorem k78_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k78_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k78_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k78_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k78_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k78_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k78_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s78_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k78_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k78_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k78_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k78_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k78_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k78_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 5 6).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k78_5_6_126 k h.1 (by omega)
theorem s78_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 5 7 = true := by decide +kernel
theorem s78_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 0 = true := by decide +kernel
theorem s78_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 1 = true := by decide +kernel
theorem s78_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 2 = true := by decide +kernel
theorem s78_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 3 = true := by decide +kernel
theorem s78_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 4 = true := by decide +kernel
theorem s78_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 5 = true := by decide +kernel
theorem s78_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 6 = true := by decide +kernel
theorem k78_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k78_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k78_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k78_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k78_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s78_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k78_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k78_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k78_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k78_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 78) ((InDA1.TCasaD 5 6 7).getD (78 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k78_6_7_12 k h.1 (by omega)
theorem col78_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 7 v) = true := by decide +kernel
theorem col78 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 78) 78 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col78_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col78_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col78_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s78_3_0
    · exact s78_3_1
    · exact s78_3_2
    · exact s78_3_3
    · exact s78_3_4
    · exact s78_3_5
    · exact s78_3_6
    · exact s78_3_7
  · fin_cases v
    · exact s78_4_0
    · exact s78_4_1
    · exact s78_4_2
    · exact s78_4_3
    · exact s78_4_4
    · exact s78_4_5
    · exact s78_4_6
    · exact s78_4_7
  · fin_cases v
    · exact s78_5_0
    · exact s78_5_1
    · exact s78_5_2
    · exact s78_5_3
    · exact s78_5_4
    · exact s78_5_5
    · exact s78_5_6
    · exact s78_5_7
  · fin_cases v
    · exact s78_6_0
    · exact s78_6_1
    · exact s78_6_2
    · exact s78_6_3
    · exact s78_6_4
    · exact s78_6_5
    · exact s78_6_6
    · exact s78_6_7
  · exact List.all_eq_true.mp col78_7 v (List.mem_finRange v)
theorem col79_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 0 v) = true := by decide +kernel
theorem col79_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 1 v) = true := by decide +kernel
theorem col79_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 2 v) = true := by decide +kernel
theorem s79_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 0 = true := by decide +kernel
theorem s79_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 1 = true := by decide +kernel
theorem s79_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 2 = true := by decide +kernel
theorem k79_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k79_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k79_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s79_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k79_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k79_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 79) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (79 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k79_3_3_26 k h.1 (by omega)
theorem s79_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 4 = true := by decide +kernel
theorem s79_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 5 = true := by decide +kernel
theorem k79_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k79_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k79_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k79_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k79_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k79_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k79_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k79_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k79_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k79_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k79_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s79_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k79_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k79_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k79_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k79_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k79_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k79_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k79_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k79_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k79_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k79_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 3 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k79_3_6_130 k h.1 (by omega)
theorem s79_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 3 7 = true := by decide +kernel
theorem s79_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 0 = true := by decide +kernel
theorem s79_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 1 = true := by decide +kernel
theorem s79_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 2 = true := by decide +kernel
theorem s79_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 3 = true := by decide +kernel
theorem s79_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 4 = true := by decide +kernel
theorem s79_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 5 = true := by decide +kernel
theorem k79_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k79_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k79_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k79_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k79_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k79_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k79_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s79_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k79_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k79_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k79_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k79_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k79_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k79_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TTsaaD 4 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k79_4_6_126 k h.1 (by omega)
theorem s79_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 4 7 = true := by decide +kernel
theorem s79_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 0 = true := by decide +kernel
theorem s79_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 1 = true := by decide +kernel
theorem s79_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 2 = true := by decide +kernel
theorem s79_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 3 = true := by decide +kernel
theorem s79_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 4 = true := by decide +kernel
theorem s79_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 5 = true := by decide +kernel
theorem k79_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k79_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k79_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k79_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k79_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k79_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k79_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s79_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k79_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k79_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k79_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k79_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k79_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k79_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 5 6).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k79_5_6_126 k h.1 (by omega)
theorem s79_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 5 7 = true := by decide +kernel
theorem s79_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 0 = true := by decide +kernel
theorem s79_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 1 = true := by decide +kernel
theorem s79_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 2 = true := by decide +kernel
theorem s79_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 3 = true := by decide +kernel
theorem s79_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 4 = true := by decide +kernel
theorem s79_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 5 = true := by decide +kernel
theorem s79_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 6 = true := by decide +kernel
theorem k79_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k79_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k79_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k79_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k79_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s79_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k79_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k79_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k79_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k79_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 79) ((InDA1.TCasaD 5 6 7).getD (79 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k79_6_7_12 k h.1 (by omega)
theorem col79_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 7 v) = true := by decide +kernel
theorem col79 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 79) 79 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col79_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col79_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col79_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s79_3_0
    · exact s79_3_1
    · exact s79_3_2
    · exact s79_3_3
    · exact s79_3_4
    · exact s79_3_5
    · exact s79_3_6
    · exact s79_3_7
  · fin_cases v
    · exact s79_4_0
    · exact s79_4_1
    · exact s79_4_2
    · exact s79_4_3
    · exact s79_4_4
    · exact s79_4_5
    · exact s79_4_6
    · exact s79_4_7
  · fin_cases v
    · exact s79_5_0
    · exact s79_5_1
    · exact s79_5_2
    · exact s79_5_3
    · exact s79_5_4
    · exact s79_5_5
    · exact s79_5_6
    · exact s79_5_7
  · fin_cases v
    · exact s79_6_0
    · exact s79_6_1
    · exact s79_6_2
    · exact s79_6_3
    · exact s79_6_4
    · exact s79_6_5
    · exact s79_6_6
    · exact s79_6_7
  · exact List.all_eq_true.mp col79_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
