module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [65, 70). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col65_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 0 v) = true := by decide +kernel
theorem col65_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 1 v) = true := by decide +kernel
theorem col65_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 2 v) = true := by decide +kernel
theorem s65_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 0 = true := by decide +kernel
theorem s65_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 1 = true := by decide +kernel
theorem s65_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 2 = true := by decide +kernel
theorem k65_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k65_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k65_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s65_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k65_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k65_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 65) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (65 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k65_3_3_26 k h.1 (by omega)
theorem s65_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 4 = true := by decide +kernel
theorem s65_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 5 = true := by decide +kernel
theorem k65_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k65_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k65_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k65_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k65_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k65_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k65_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k65_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k65_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k65_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k65_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s65_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k65_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k65_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k65_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k65_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k65_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k65_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k65_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k65_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k65_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k65_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 3 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k65_3_6_130 k h.1 (by omega)
theorem s65_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 3 7 = true := by decide +kernel
theorem s65_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 0 = true := by decide +kernel
theorem s65_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 1 = true := by decide +kernel
theorem s65_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 2 = true := by decide +kernel
theorem s65_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 3 = true := by decide +kernel
theorem s65_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 4 = true := by decide +kernel
theorem s65_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 5 = true := by decide +kernel
theorem k65_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k65_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k65_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k65_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k65_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k65_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k65_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s65_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k65_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k65_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k65_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k65_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k65_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k65_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TTsaaD 4 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k65_4_6_126 k h.1 (by omega)
theorem s65_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 4 7 = true := by decide +kernel
theorem s65_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 0 = true := by decide +kernel
theorem s65_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 1 = true := by decide +kernel
theorem s65_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 2 = true := by decide +kernel
theorem s65_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 3 = true := by decide +kernel
theorem s65_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 4 = true := by decide +kernel
theorem s65_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 5 = true := by decide +kernel
theorem k65_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k65_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k65_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k65_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k65_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k65_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k65_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s65_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k65_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k65_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k65_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k65_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k65_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k65_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 5 6).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k65_5_6_126 k h.1 (by omega)
theorem s65_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 5 7 = true := by decide +kernel
theorem s65_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 0 = true := by decide +kernel
theorem s65_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 1 = true := by decide +kernel
theorem s65_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 2 = true := by decide +kernel
theorem s65_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 3 = true := by decide +kernel
theorem s65_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 4 = true := by decide +kernel
theorem s65_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 5 = true := by decide +kernel
theorem s65_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 6 = true := by decide +kernel
theorem k65_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k65_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k65_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k65_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k65_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s65_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k65_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k65_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k65_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k65_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 65) ((InDA1.TCasaD 5 6 7).getD (65 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k65_6_7_12 k h.1 (by omega)
theorem col65_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 7 v) = true := by decide +kernel
theorem col65 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 65) 65 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col65_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col65_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col65_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s65_3_0
    · exact s65_3_1
    · exact s65_3_2
    · exact s65_3_3
    · exact s65_3_4
    · exact s65_3_5
    · exact s65_3_6
    · exact s65_3_7
  · fin_cases v
    · exact s65_4_0
    · exact s65_4_1
    · exact s65_4_2
    · exact s65_4_3
    · exact s65_4_4
    · exact s65_4_5
    · exact s65_4_6
    · exact s65_4_7
  · fin_cases v
    · exact s65_5_0
    · exact s65_5_1
    · exact s65_5_2
    · exact s65_5_3
    · exact s65_5_4
    · exact s65_5_5
    · exact s65_5_6
    · exact s65_5_7
  · fin_cases v
    · exact s65_6_0
    · exact s65_6_1
    · exact s65_6_2
    · exact s65_6_3
    · exact s65_6_4
    · exact s65_6_5
    · exact s65_6_6
    · exact s65_6_7
  · exact List.all_eq_true.mp col65_7 v (List.mem_finRange v)
theorem col66_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 0 v) = true := by decide +kernel
theorem col66_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 1 v) = true := by decide +kernel
theorem col66_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 2 v) = true := by decide +kernel
theorem s66_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 0 = true := by decide +kernel
theorem s66_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 1 = true := by decide +kernel
theorem s66_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 2 = true := by decide +kernel
theorem k66_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k66_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k66_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s66_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k66_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k66_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 66) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (66 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k66_3_3_26 k h.1 (by omega)
theorem s66_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 4 = true := by decide +kernel
theorem s66_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 5 = true := by decide +kernel
theorem k66_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k66_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k66_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k66_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k66_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k66_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k66_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k66_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k66_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k66_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k66_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s66_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k66_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k66_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k66_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k66_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k66_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k66_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k66_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k66_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k66_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k66_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 3 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k66_3_6_130 k h.1 (by omega)
theorem s66_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 3 7 = true := by decide +kernel
theorem s66_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 0 = true := by decide +kernel
theorem s66_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 1 = true := by decide +kernel
theorem s66_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 2 = true := by decide +kernel
theorem s66_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 3 = true := by decide +kernel
theorem s66_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 4 = true := by decide +kernel
theorem s66_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 5 = true := by decide +kernel
theorem k66_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k66_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k66_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k66_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k66_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k66_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k66_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s66_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k66_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k66_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k66_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k66_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k66_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k66_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TTsaaD 4 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k66_4_6_126 k h.1 (by omega)
theorem s66_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 4 7 = true := by decide +kernel
theorem s66_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 0 = true := by decide +kernel
theorem s66_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 1 = true := by decide +kernel
theorem s66_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 2 = true := by decide +kernel
theorem s66_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 3 = true := by decide +kernel
theorem s66_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 4 = true := by decide +kernel
theorem s66_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 5 = true := by decide +kernel
theorem k66_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k66_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k66_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k66_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k66_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k66_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k66_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s66_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k66_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k66_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k66_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k66_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k66_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k66_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 5 6).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k66_5_6_126 k h.1 (by omega)
theorem s66_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 5 7 = true := by decide +kernel
theorem s66_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 0 = true := by decide +kernel
theorem s66_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 1 = true := by decide +kernel
theorem s66_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 2 = true := by decide +kernel
theorem s66_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 3 = true := by decide +kernel
theorem s66_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 4 = true := by decide +kernel
theorem s66_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 5 = true := by decide +kernel
theorem s66_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 6 = true := by decide +kernel
theorem k66_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k66_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k66_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k66_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k66_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s66_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k66_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k66_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k66_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k66_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 66) ((InDA1.TCasaD 5 6 7).getD (66 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k66_6_7_12 k h.1 (by omega)
theorem col66_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 7 v) = true := by decide +kernel
theorem col66 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 66) 66 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col66_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col66_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col66_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s66_3_0
    · exact s66_3_1
    · exact s66_3_2
    · exact s66_3_3
    · exact s66_3_4
    · exact s66_3_5
    · exact s66_3_6
    · exact s66_3_7
  · fin_cases v
    · exact s66_4_0
    · exact s66_4_1
    · exact s66_4_2
    · exact s66_4_3
    · exact s66_4_4
    · exact s66_4_5
    · exact s66_4_6
    · exact s66_4_7
  · fin_cases v
    · exact s66_5_0
    · exact s66_5_1
    · exact s66_5_2
    · exact s66_5_3
    · exact s66_5_4
    · exact s66_5_5
    · exact s66_5_6
    · exact s66_5_7
  · fin_cases v
    · exact s66_6_0
    · exact s66_6_1
    · exact s66_6_2
    · exact s66_6_3
    · exact s66_6_4
    · exact s66_6_5
    · exact s66_6_6
    · exact s66_6_7
  · exact List.all_eq_true.mp col66_7 v (List.mem_finRange v)
theorem col67_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 0 v) = true := by decide +kernel
theorem col67_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 1 v) = true := by decide +kernel
theorem col67_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 2 v) = true := by decide +kernel
theorem s67_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 0 = true := by decide +kernel
theorem s67_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 1 = true := by decide +kernel
theorem s67_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 2 = true := by decide +kernel
theorem k67_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k67_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k67_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s67_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k67_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k67_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 67) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (67 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k67_3_3_26 k h.1 (by omega)
theorem s67_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 4 = true := by decide +kernel
theorem s67_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 5 = true := by decide +kernel
theorem k67_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k67_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k67_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k67_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k67_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k67_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k67_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k67_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k67_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k67_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k67_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s67_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k67_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k67_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k67_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k67_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k67_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k67_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k67_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k67_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k67_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k67_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 3 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k67_3_6_130 k h.1 (by omega)
theorem s67_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 3 7 = true := by decide +kernel
theorem s67_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 0 = true := by decide +kernel
theorem s67_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 1 = true := by decide +kernel
theorem s67_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 2 = true := by decide +kernel
theorem s67_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 3 = true := by decide +kernel
theorem s67_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 4 = true := by decide +kernel
theorem s67_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 5 = true := by decide +kernel
theorem k67_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k67_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k67_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k67_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k67_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k67_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k67_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s67_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k67_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k67_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k67_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k67_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k67_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k67_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TTsaaD 4 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k67_4_6_126 k h.1 (by omega)
theorem s67_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 4 7 = true := by decide +kernel
theorem s67_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 0 = true := by decide +kernel
theorem s67_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 1 = true := by decide +kernel
theorem s67_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 2 = true := by decide +kernel
theorem s67_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 3 = true := by decide +kernel
theorem s67_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 4 = true := by decide +kernel
theorem s67_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 5 = true := by decide +kernel
theorem k67_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k67_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k67_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k67_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k67_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k67_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k67_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s67_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k67_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k67_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k67_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k67_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k67_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k67_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 5 6).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k67_5_6_126 k h.1 (by omega)
theorem s67_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 5 7 = true := by decide +kernel
theorem s67_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 0 = true := by decide +kernel
theorem s67_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 1 = true := by decide +kernel
theorem s67_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 2 = true := by decide +kernel
theorem s67_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 3 = true := by decide +kernel
theorem s67_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 4 = true := by decide +kernel
theorem s67_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 5 = true := by decide +kernel
theorem s67_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 6 = true := by decide +kernel
theorem k67_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k67_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k67_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k67_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k67_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s67_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k67_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k67_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k67_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k67_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 67) ((InDA1.TCasaD 5 6 7).getD (67 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k67_6_7_12 k h.1 (by omega)
theorem col67_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 7 v) = true := by decide +kernel
theorem col67 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 67) 67 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col67_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col67_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col67_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s67_3_0
    · exact s67_3_1
    · exact s67_3_2
    · exact s67_3_3
    · exact s67_3_4
    · exact s67_3_5
    · exact s67_3_6
    · exact s67_3_7
  · fin_cases v
    · exact s67_4_0
    · exact s67_4_1
    · exact s67_4_2
    · exact s67_4_3
    · exact s67_4_4
    · exact s67_4_5
    · exact s67_4_6
    · exact s67_4_7
  · fin_cases v
    · exact s67_5_0
    · exact s67_5_1
    · exact s67_5_2
    · exact s67_5_3
    · exact s67_5_4
    · exact s67_5_5
    · exact s67_5_6
    · exact s67_5_7
  · fin_cases v
    · exact s67_6_0
    · exact s67_6_1
    · exact s67_6_2
    · exact s67_6_3
    · exact s67_6_4
    · exact s67_6_5
    · exact s67_6_6
    · exact s67_6_7
  · exact List.all_eq_true.mp col67_7 v (List.mem_finRange v)
theorem col68_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 0 v) = true := by decide +kernel
theorem col68_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 1 v) = true := by decide +kernel
theorem col68_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 2 v) = true := by decide +kernel
theorem s68_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 0 = true := by decide +kernel
theorem s68_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 1 = true := by decide +kernel
theorem s68_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 2 = true := by decide +kernel
theorem k68_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k68_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k68_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s68_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k68_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k68_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 68) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (68 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k68_3_3_26 k h.1 (by omega)
theorem s68_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 4 = true := by decide +kernel
theorem s68_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 5 = true := by decide +kernel
theorem k68_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k68_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k68_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k68_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k68_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k68_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k68_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k68_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k68_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k68_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k68_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s68_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k68_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k68_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k68_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k68_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k68_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k68_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k68_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k68_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k68_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k68_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 3 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k68_3_6_130 k h.1 (by omega)
theorem s68_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 3 7 = true := by decide +kernel
theorem s68_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 0 = true := by decide +kernel
theorem s68_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 1 = true := by decide +kernel
theorem s68_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 2 = true := by decide +kernel
theorem s68_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 3 = true := by decide +kernel
theorem s68_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 4 = true := by decide +kernel
theorem s68_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 5 = true := by decide +kernel
theorem k68_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k68_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k68_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k68_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k68_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k68_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k68_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s68_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k68_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k68_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k68_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k68_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k68_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k68_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TTsaaD 4 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k68_4_6_126 k h.1 (by omega)
theorem s68_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 4 7 = true := by decide +kernel
theorem s68_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 0 = true := by decide +kernel
theorem s68_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 1 = true := by decide +kernel
theorem s68_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 2 = true := by decide +kernel
theorem s68_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 3 = true := by decide +kernel
theorem s68_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 4 = true := by decide +kernel
theorem s68_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 5 = true := by decide +kernel
theorem k68_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k68_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k68_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k68_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k68_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k68_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k68_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s68_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k68_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k68_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k68_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k68_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k68_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k68_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 5 6).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k68_5_6_126 k h.1 (by omega)
theorem s68_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 5 7 = true := by decide +kernel
theorem s68_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 0 = true := by decide +kernel
theorem s68_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 1 = true := by decide +kernel
theorem s68_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 2 = true := by decide +kernel
theorem s68_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 3 = true := by decide +kernel
theorem s68_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 4 = true := by decide +kernel
theorem s68_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 5 = true := by decide +kernel
theorem s68_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 6 = true := by decide +kernel
theorem k68_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k68_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k68_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k68_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k68_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s68_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k68_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k68_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k68_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k68_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 68) ((InDA1.TCasaD 5 6 7).getD (68 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k68_6_7_12 k h.1 (by omega)
theorem col68_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 7 v) = true := by decide +kernel
theorem col68 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 68) 68 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col68_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col68_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col68_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s68_3_0
    · exact s68_3_1
    · exact s68_3_2
    · exact s68_3_3
    · exact s68_3_4
    · exact s68_3_5
    · exact s68_3_6
    · exact s68_3_7
  · fin_cases v
    · exact s68_4_0
    · exact s68_4_1
    · exact s68_4_2
    · exact s68_4_3
    · exact s68_4_4
    · exact s68_4_5
    · exact s68_4_6
    · exact s68_4_7
  · fin_cases v
    · exact s68_5_0
    · exact s68_5_1
    · exact s68_5_2
    · exact s68_5_3
    · exact s68_5_4
    · exact s68_5_5
    · exact s68_5_6
    · exact s68_5_7
  · fin_cases v
    · exact s68_6_0
    · exact s68_6_1
    · exact s68_6_2
    · exact s68_6_3
    · exact s68_6_4
    · exact s68_6_5
    · exact s68_6_6
    · exact s68_6_7
  · exact List.all_eq_true.mp col68_7 v (List.mem_finRange v)
theorem col69_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 0 v) = true := by decide +kernel
theorem col69_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 1 v) = true := by decide +kernel
theorem col69_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 2 v) = true := by decide +kernel
theorem s69_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 0 = true := by decide +kernel
theorem s69_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 1 = true := by decide +kernel
theorem s69_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 2 = true := by decide +kernel
theorem k69_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k69_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k69_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s69_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k69_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k69_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 69) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (69 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k69_3_3_26 k h.1 (by omega)
theorem s69_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 4 = true := by decide +kernel
theorem s69_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 5 = true := by decide +kernel
theorem k69_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k69_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k69_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k69_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k69_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k69_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k69_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k69_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k69_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k69_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k69_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s69_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k69_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k69_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k69_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k69_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k69_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k69_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k69_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k69_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k69_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k69_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 3 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k69_3_6_130 k h.1 (by omega)
theorem s69_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 3 7 = true := by decide +kernel
theorem s69_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 0 = true := by decide +kernel
theorem s69_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 1 = true := by decide +kernel
theorem s69_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 2 = true := by decide +kernel
theorem s69_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 3 = true := by decide +kernel
theorem s69_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 4 = true := by decide +kernel
theorem s69_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 5 = true := by decide +kernel
theorem k69_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k69_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k69_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k69_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k69_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k69_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k69_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s69_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k69_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k69_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k69_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k69_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k69_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k69_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TTsaaD 4 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k69_4_6_126 k h.1 (by omega)
theorem s69_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 4 7 = true := by decide +kernel
theorem s69_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 0 = true := by decide +kernel
theorem s69_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 1 = true := by decide +kernel
theorem s69_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 2 = true := by decide +kernel
theorem s69_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 3 = true := by decide +kernel
theorem s69_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 4 = true := by decide +kernel
theorem s69_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 5 = true := by decide +kernel
theorem k69_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k69_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k69_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k69_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k69_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k69_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k69_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s69_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k69_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k69_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k69_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k69_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k69_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k69_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 5 6).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k69_5_6_126 k h.1 (by omega)
theorem s69_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 5 7 = true := by decide +kernel
theorem s69_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 0 = true := by decide +kernel
theorem s69_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 1 = true := by decide +kernel
theorem s69_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 2 = true := by decide +kernel
theorem s69_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 3 = true := by decide +kernel
theorem s69_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 4 = true := by decide +kernel
theorem s69_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 5 = true := by decide +kernel
theorem s69_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 6 = true := by decide +kernel
theorem k69_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k69_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k69_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k69_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k69_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s69_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k69_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k69_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k69_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k69_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 69) ((InDA1.TCasaD 5 6 7).getD (69 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k69_6_7_12 k h.1 (by omega)
theorem col69_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 7 v) = true := by decide +kernel
theorem col69 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 69) 69 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col69_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col69_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col69_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s69_3_0
    · exact s69_3_1
    · exact s69_3_2
    · exact s69_3_3
    · exact s69_3_4
    · exact s69_3_5
    · exact s69_3_6
    · exact s69_3_7
  · fin_cases v
    · exact s69_4_0
    · exact s69_4_1
    · exact s69_4_2
    · exact s69_4_3
    · exact s69_4_4
    · exact s69_4_5
    · exact s69_4_6
    · exact s69_4_7
  · fin_cases v
    · exact s69_5_0
    · exact s69_5_1
    · exact s69_5_2
    · exact s69_5_3
    · exact s69_5_4
    · exact s69_5_5
    · exact s69_5_6
    · exact s69_5_7
  · fin_cases v
    · exact s69_6_0
    · exact s69_6_1
    · exact s69_6_2
    · exact s69_6_3
    · exact s69_6_4
    · exact s69_6_5
    · exact s69_6_6
    · exact s69_6_7
  · exact List.all_eq_true.mp col69_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
