module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [55, 60). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col55_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 0 v) = true := by decide +kernel
theorem col55_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 1 v) = true := by decide +kernel
theorem col55_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 2 v) = true := by decide +kernel
theorem s55_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 0 = true := by decide +kernel
theorem s55_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 1 = true := by decide +kernel
theorem s55_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 2 = true := by decide +kernel
theorem k55_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k55_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k55_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s55_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k55_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k55_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 55) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (55 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k55_3_3_26 k h.1 (by omega)
theorem s55_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 4 = true := by decide +kernel
theorem s55_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 5 = true := by decide +kernel
theorem k55_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k55_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k55_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k55_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k55_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k55_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k55_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k55_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k55_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k55_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k55_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s55_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k55_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k55_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k55_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k55_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k55_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k55_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k55_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k55_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k55_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k55_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TTsaaD 3 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k55_3_6_130 k h.1 (by omega)
theorem s55_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 3 7 = true := by decide +kernel
theorem s55_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 0 = true := by decide +kernel
theorem s55_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 1 = true := by decide +kernel
theorem s55_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 2 = true := by decide +kernel
theorem s55_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 3 = true := by decide +kernel
theorem s55_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 4 = true := by decide +kernel
theorem s55_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 5 = true := by decide +kernel
theorem k55_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k55_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k55_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k55_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k55_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k55_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k55_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s55_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k55_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k55_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k55_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k55_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k55_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k55_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 4 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k55_4_6_126 k h.1 (by omega)
theorem s55_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 4 7 = true := by decide +kernel
theorem s55_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 0 = true := by decide +kernel
theorem s55_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 1 = true := by decide +kernel
theorem s55_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 2 = true := by decide +kernel
theorem s55_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 3 = true := by decide +kernel
theorem s55_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 4 = true := by decide +kernel
theorem s55_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 5 = true := by decide +kernel
theorem k55_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k55_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k55_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k55_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k55_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k55_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k55_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s55_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k55_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k55_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k55_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k55_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k55_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k55_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 5 6).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k55_5_6_126 k h.1 (by omega)
theorem s55_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 5 7 = true := by decide +kernel
theorem s55_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 0 = true := by decide +kernel
theorem s55_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 1 = true := by decide +kernel
theorem s55_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 2 = true := by decide +kernel
theorem s55_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 3 = true := by decide +kernel
theorem s55_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 4 = true := by decide +kernel
theorem s55_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 5 = true := by decide +kernel
theorem s55_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 6 = true := by decide +kernel
theorem k55_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k55_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k55_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k55_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k55_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s55_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k55_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k55_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k55_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k55_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 55) ((InDA1.TCasaD 4 6 7).getD (55 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k55_6_7_12 k h.1 (by omega)
theorem col55_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 7 v) = true := by decide +kernel
theorem col55 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 55) 55 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col55_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col55_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col55_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s55_3_0
    · exact s55_3_1
    · exact s55_3_2
    · exact s55_3_3
    · exact s55_3_4
    · exact s55_3_5
    · exact s55_3_6
    · exact s55_3_7
  · fin_cases v
    · exact s55_4_0
    · exact s55_4_1
    · exact s55_4_2
    · exact s55_4_3
    · exact s55_4_4
    · exact s55_4_5
    · exact s55_4_6
    · exact s55_4_7
  · fin_cases v
    · exact s55_5_0
    · exact s55_5_1
    · exact s55_5_2
    · exact s55_5_3
    · exact s55_5_4
    · exact s55_5_5
    · exact s55_5_6
    · exact s55_5_7
  · fin_cases v
    · exact s55_6_0
    · exact s55_6_1
    · exact s55_6_2
    · exact s55_6_3
    · exact s55_6_4
    · exact s55_6_5
    · exact s55_6_6
    · exact s55_6_7
  · exact List.all_eq_true.mp col55_7 v (List.mem_finRange v)
theorem col56_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 0 v) = true := by decide +kernel
theorem col56_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 1 v) = true := by decide +kernel
theorem col56_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 2 v) = true := by decide +kernel
theorem s56_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 0 = true := by decide +kernel
theorem s56_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 1 = true := by decide +kernel
theorem s56_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 2 = true := by decide +kernel
theorem k56_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k56_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k56_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s56_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k56_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k56_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 56) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (56 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k56_3_3_26 k h.1 (by omega)
theorem s56_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 4 = true := by decide +kernel
theorem s56_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 5 = true := by decide +kernel
theorem k56_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k56_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k56_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k56_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k56_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k56_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k56_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k56_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k56_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k56_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k56_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s56_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k56_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k56_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k56_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k56_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k56_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k56_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k56_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k56_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k56_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k56_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TTsaaD 3 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k56_3_6_130 k h.1 (by omega)
theorem s56_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 3 7 = true := by decide +kernel
theorem s56_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 0 = true := by decide +kernel
theorem s56_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 1 = true := by decide +kernel
theorem s56_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 2 = true := by decide +kernel
theorem s56_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 3 = true := by decide +kernel
theorem s56_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 4 = true := by decide +kernel
theorem s56_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 5 = true := by decide +kernel
theorem k56_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k56_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k56_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k56_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k56_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k56_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k56_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s56_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k56_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k56_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k56_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k56_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k56_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k56_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 4 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k56_4_6_126 k h.1 (by omega)
theorem s56_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 4 7 = true := by decide +kernel
theorem s56_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 0 = true := by decide +kernel
theorem s56_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 1 = true := by decide +kernel
theorem s56_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 2 = true := by decide +kernel
theorem s56_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 3 = true := by decide +kernel
theorem s56_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 4 = true := by decide +kernel
theorem s56_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 5 = true := by decide +kernel
theorem k56_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k56_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k56_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k56_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k56_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k56_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k56_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s56_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k56_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k56_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k56_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k56_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k56_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k56_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 5 6).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k56_5_6_126 k h.1 (by omega)
theorem s56_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 5 7 = true := by decide +kernel
theorem s56_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 0 = true := by decide +kernel
theorem s56_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 1 = true := by decide +kernel
theorem s56_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 2 = true := by decide +kernel
theorem s56_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 3 = true := by decide +kernel
theorem s56_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 4 = true := by decide +kernel
theorem s56_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 5 = true := by decide +kernel
theorem s56_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 6 = true := by decide +kernel
theorem k56_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k56_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k56_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k56_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k56_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s56_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k56_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k56_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k56_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k56_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 56) ((InDA1.TCasaD 4 6 7).getD (56 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k56_6_7_12 k h.1 (by omega)
theorem col56_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 7 v) = true := by decide +kernel
theorem col56 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 56) 56 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col56_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col56_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col56_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s56_3_0
    · exact s56_3_1
    · exact s56_3_2
    · exact s56_3_3
    · exact s56_3_4
    · exact s56_3_5
    · exact s56_3_6
    · exact s56_3_7
  · fin_cases v
    · exact s56_4_0
    · exact s56_4_1
    · exact s56_4_2
    · exact s56_4_3
    · exact s56_4_4
    · exact s56_4_5
    · exact s56_4_6
    · exact s56_4_7
  · fin_cases v
    · exact s56_5_0
    · exact s56_5_1
    · exact s56_5_2
    · exact s56_5_3
    · exact s56_5_4
    · exact s56_5_5
    · exact s56_5_6
    · exact s56_5_7
  · fin_cases v
    · exact s56_6_0
    · exact s56_6_1
    · exact s56_6_2
    · exact s56_6_3
    · exact s56_6_4
    · exact s56_6_5
    · exact s56_6_6
    · exact s56_6_7
  · exact List.all_eq_true.mp col56_7 v (List.mem_finRange v)
theorem col57_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 0 v) = true := by decide +kernel
theorem col57_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 1 v) = true := by decide +kernel
theorem col57_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 2 v) = true := by decide +kernel
theorem s57_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 0 = true := by decide +kernel
theorem s57_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 1 = true := by decide +kernel
theorem s57_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 2 = true := by decide +kernel
theorem k57_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k57_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k57_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s57_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k57_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k57_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 57) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (57 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k57_3_3_26 k h.1 (by omega)
theorem s57_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 4 = true := by decide +kernel
theorem s57_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 5 = true := by decide +kernel
theorem k57_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k57_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k57_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k57_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k57_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k57_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k57_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k57_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k57_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k57_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k57_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s57_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k57_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k57_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k57_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k57_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k57_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k57_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k57_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k57_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k57_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k57_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TTsaaD 3 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k57_3_6_130 k h.1 (by omega)
theorem s57_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 3 7 = true := by decide +kernel
theorem s57_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 0 = true := by decide +kernel
theorem s57_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 1 = true := by decide +kernel
theorem s57_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 2 = true := by decide +kernel
theorem s57_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 3 = true := by decide +kernel
theorem s57_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 4 = true := by decide +kernel
theorem s57_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 5 = true := by decide +kernel
theorem k57_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k57_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k57_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k57_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k57_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k57_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k57_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s57_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k57_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k57_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k57_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k57_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k57_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k57_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 4 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k57_4_6_126 k h.1 (by omega)
theorem s57_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 4 7 = true := by decide +kernel
theorem s57_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 0 = true := by decide +kernel
theorem s57_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 1 = true := by decide +kernel
theorem s57_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 2 = true := by decide +kernel
theorem s57_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 3 = true := by decide +kernel
theorem s57_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 4 = true := by decide +kernel
theorem s57_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 5 = true := by decide +kernel
theorem k57_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k57_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k57_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k57_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k57_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k57_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k57_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s57_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k57_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k57_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k57_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k57_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k57_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k57_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 5 6).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k57_5_6_126 k h.1 (by omega)
theorem s57_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 5 7 = true := by decide +kernel
theorem s57_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 0 = true := by decide +kernel
theorem s57_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 1 = true := by decide +kernel
theorem s57_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 2 = true := by decide +kernel
theorem s57_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 3 = true := by decide +kernel
theorem s57_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 4 = true := by decide +kernel
theorem s57_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 5 = true := by decide +kernel
theorem s57_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 6 = true := by decide +kernel
theorem k57_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k57_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k57_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k57_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k57_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s57_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k57_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k57_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k57_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k57_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 57) ((InDA1.TCasaD 4 6 7).getD (57 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k57_6_7_12 k h.1 (by omega)
theorem col57_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 7 v) = true := by decide +kernel
theorem col57 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 57) 57 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col57_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col57_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col57_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s57_3_0
    · exact s57_3_1
    · exact s57_3_2
    · exact s57_3_3
    · exact s57_3_4
    · exact s57_3_5
    · exact s57_3_6
    · exact s57_3_7
  · fin_cases v
    · exact s57_4_0
    · exact s57_4_1
    · exact s57_4_2
    · exact s57_4_3
    · exact s57_4_4
    · exact s57_4_5
    · exact s57_4_6
    · exact s57_4_7
  · fin_cases v
    · exact s57_5_0
    · exact s57_5_1
    · exact s57_5_2
    · exact s57_5_3
    · exact s57_5_4
    · exact s57_5_5
    · exact s57_5_6
    · exact s57_5_7
  · fin_cases v
    · exact s57_6_0
    · exact s57_6_1
    · exact s57_6_2
    · exact s57_6_3
    · exact s57_6_4
    · exact s57_6_5
    · exact s57_6_6
    · exact s57_6_7
  · exact List.all_eq_true.mp col57_7 v (List.mem_finRange v)
theorem col58_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 0 v) = true := by decide +kernel
theorem col58_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 1 v) = true := by decide +kernel
theorem col58_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 2 v) = true := by decide +kernel
theorem s58_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 0 = true := by decide +kernel
theorem s58_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 1 = true := by decide +kernel
theorem s58_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 2 = true := by decide +kernel
theorem k58_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k58_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k58_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s58_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k58_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k58_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 58) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (58 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k58_3_3_26 k h.1 (by omega)
theorem s58_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 4 = true := by decide +kernel
theorem s58_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 5 = true := by decide +kernel
theorem k58_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k58_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k58_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k58_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k58_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k58_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k58_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k58_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k58_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k58_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k58_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s58_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k58_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k58_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k58_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k58_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k58_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k58_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k58_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k58_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k58_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k58_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TTsaaD 3 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k58_3_6_130 k h.1 (by omega)
theorem s58_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 3 7 = true := by decide +kernel
theorem s58_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 0 = true := by decide +kernel
theorem s58_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 1 = true := by decide +kernel
theorem s58_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 2 = true := by decide +kernel
theorem s58_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 3 = true := by decide +kernel
theorem s58_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 4 = true := by decide +kernel
theorem s58_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 5 = true := by decide +kernel
theorem k58_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k58_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k58_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k58_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k58_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k58_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k58_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s58_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k58_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k58_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k58_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k58_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k58_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k58_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 4 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k58_4_6_126 k h.1 (by omega)
theorem s58_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 4 7 = true := by decide +kernel
theorem s58_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 0 = true := by decide +kernel
theorem s58_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 1 = true := by decide +kernel
theorem s58_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 2 = true := by decide +kernel
theorem s58_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 3 = true := by decide +kernel
theorem s58_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 4 = true := by decide +kernel
theorem s58_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 5 = true := by decide +kernel
theorem k58_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k58_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k58_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k58_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k58_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k58_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k58_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s58_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k58_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k58_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k58_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k58_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k58_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k58_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 5 6).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k58_5_6_126 k h.1 (by omega)
theorem s58_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 5 7 = true := by decide +kernel
theorem s58_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 0 = true := by decide +kernel
theorem s58_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 1 = true := by decide +kernel
theorem s58_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 2 = true := by decide +kernel
theorem s58_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 3 = true := by decide +kernel
theorem s58_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 4 = true := by decide +kernel
theorem s58_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 5 = true := by decide +kernel
theorem s58_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 6 = true := by decide +kernel
theorem k58_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k58_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k58_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k58_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k58_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s58_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k58_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k58_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k58_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k58_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 58) ((InDA1.TCasaD 4 6 7).getD (58 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k58_6_7_12 k h.1 (by omega)
theorem col58_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 7 v) = true := by decide +kernel
theorem col58 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 58) 58 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col58_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col58_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col58_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s58_3_0
    · exact s58_3_1
    · exact s58_3_2
    · exact s58_3_3
    · exact s58_3_4
    · exact s58_3_5
    · exact s58_3_6
    · exact s58_3_7
  · fin_cases v
    · exact s58_4_0
    · exact s58_4_1
    · exact s58_4_2
    · exact s58_4_3
    · exact s58_4_4
    · exact s58_4_5
    · exact s58_4_6
    · exact s58_4_7
  · fin_cases v
    · exact s58_5_0
    · exact s58_5_1
    · exact s58_5_2
    · exact s58_5_3
    · exact s58_5_4
    · exact s58_5_5
    · exact s58_5_6
    · exact s58_5_7
  · fin_cases v
    · exact s58_6_0
    · exact s58_6_1
    · exact s58_6_2
    · exact s58_6_3
    · exact s58_6_4
    · exact s58_6_5
    · exact s58_6_6
    · exact s58_6_7
  · exact List.all_eq_true.mp col58_7 v (List.mem_finRange v)
theorem col59_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 0 v) = true := by decide +kernel
theorem col59_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 1 v) = true := by decide +kernel
theorem col59_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 2 v) = true := by decide +kernel
theorem s59_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 0 = true := by decide +kernel
theorem s59_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 1 = true := by decide +kernel
theorem s59_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 2 = true := by decide +kernel
theorem k59_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k59_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k59_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s59_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k59_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k59_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 59) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (59 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k59_3_3_26 k h.1 (by omega)
theorem s59_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 4 = true := by decide +kernel
theorem s59_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 5 = true := by decide +kernel
theorem k59_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k59_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k59_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k59_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k59_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k59_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k59_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k59_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k59_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k59_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k59_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s59_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k59_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k59_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k59_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k59_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k59_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k59_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k59_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k59_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k59_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k59_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 3 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k59_3_6_130 k h.1 (by omega)
theorem s59_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 3 7 = true := by decide +kernel
theorem s59_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 0 = true := by decide +kernel
theorem s59_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 1 = true := by decide +kernel
theorem s59_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 2 = true := by decide +kernel
theorem s59_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 3 = true := by decide +kernel
theorem s59_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 4 = true := by decide +kernel
theorem s59_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 5 = true := by decide +kernel
theorem k59_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k59_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k59_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k59_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k59_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k59_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k59_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s59_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k59_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k59_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k59_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k59_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k59_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k59_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TTsaaD 4 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k59_4_6_126 k h.1 (by omega)
theorem s59_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 4 7 = true := by decide +kernel
theorem s59_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 0 = true := by decide +kernel
theorem s59_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 1 = true := by decide +kernel
theorem s59_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 2 = true := by decide +kernel
theorem s59_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 3 = true := by decide +kernel
theorem s59_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 4 = true := by decide +kernel
theorem s59_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 5 = true := by decide +kernel
theorem k59_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k59_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k59_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k59_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k59_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k59_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k59_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s59_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k59_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k59_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k59_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k59_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k59_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k59_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 5 6).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k59_5_6_126 k h.1 (by omega)
theorem s59_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 5 7 = true := by decide +kernel
theorem s59_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 0 = true := by decide +kernel
theorem s59_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 1 = true := by decide +kernel
theorem s59_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 2 = true := by decide +kernel
theorem s59_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 3 = true := by decide +kernel
theorem s59_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 4 = true := by decide +kernel
theorem s59_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 5 = true := by decide +kernel
theorem s59_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 6 = true := by decide +kernel
theorem k59_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k59_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k59_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k59_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k59_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s59_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k59_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k59_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k59_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k59_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 59) ((InDA1.TCasaD 5 6 7).getD (59 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k59_6_7_12 k h.1 (by omega)
theorem col59_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 7 v) = true := by decide +kernel
theorem col59 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 59) 59 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col59_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col59_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col59_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s59_3_0
    · exact s59_3_1
    · exact s59_3_2
    · exact s59_3_3
    · exact s59_3_4
    · exact s59_3_5
    · exact s59_3_6
    · exact s59_3_7
  · fin_cases v
    · exact s59_4_0
    · exact s59_4_1
    · exact s59_4_2
    · exact s59_4_3
    · exact s59_4_4
    · exact s59_4_5
    · exact s59_4_6
    · exact s59_4_7
  · fin_cases v
    · exact s59_5_0
    · exact s59_5_1
    · exact s59_5_2
    · exact s59_5_3
    · exact s59_5_4
    · exact s59_5_5
    · exact s59_5_6
    · exact s59_5_7
  · fin_cases v
    · exact s59_6_0
    · exact s59_6_1
    · exact s59_6_2
    · exact s59_6_3
    · exact s59_6_4
    · exact s59_6_5
    · exact s59_6_6
    · exact s59_6_7
  · exact List.all_eq_true.mp col59_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
