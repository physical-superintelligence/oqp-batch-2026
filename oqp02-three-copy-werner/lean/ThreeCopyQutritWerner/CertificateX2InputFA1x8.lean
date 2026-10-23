module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [40, 45). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col40_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 0 v) = true := by decide +kernel
theorem col40_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 1 v) = true := by decide +kernel
theorem col40_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 2 v) = true := by decide +kernel
theorem s40_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 0 = true := by decide +kernel
theorem s40_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 1 = true := by decide +kernel
theorem s40_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 2 = true := by decide +kernel
theorem k40_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k40_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k40_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s40_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k40_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k40_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 40) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (40 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k40_3_3_26 k h.1 (by omega)
theorem s40_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 4 = true := by decide +kernel
theorem s40_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 5 = true := by decide +kernel
theorem k40_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k40_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k40_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k40_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k40_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k40_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k40_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k40_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k40_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k40_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k40_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s40_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k40_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k40_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k40_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k40_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k40_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k40_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k40_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k40_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k40_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k40_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TTsaaD 3 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k40_3_6_130 k h.1 (by omega)
theorem s40_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 3 7 = true := by decide +kernel
theorem s40_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 0 = true := by decide +kernel
theorem s40_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 1 = true := by decide +kernel
theorem s40_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 2 = true := by decide +kernel
theorem s40_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 3 = true := by decide +kernel
theorem s40_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 4 = true := by decide +kernel
theorem s40_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 5 = true := by decide +kernel
theorem k40_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k40_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k40_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k40_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k40_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k40_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k40_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s40_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k40_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k40_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k40_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k40_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k40_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k40_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 4 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k40_4_6_126 k h.1 (by omega)
theorem s40_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 4 7 = true := by decide +kernel
theorem s40_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 0 = true := by decide +kernel
theorem s40_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 1 = true := by decide +kernel
theorem s40_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 2 = true := by decide +kernel
theorem s40_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 3 = true := by decide +kernel
theorem s40_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 4 = true := by decide +kernel
theorem s40_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 5 = true := by decide +kernel
theorem k40_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k40_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k40_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k40_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k40_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k40_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k40_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s40_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k40_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k40_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k40_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k40_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k40_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k40_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 5 6).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k40_5_6_126 k h.1 (by omega)
theorem s40_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 5 7 = true := by decide +kernel
theorem s40_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 0 = true := by decide +kernel
theorem s40_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 1 = true := by decide +kernel
theorem s40_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 2 = true := by decide +kernel
theorem s40_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 3 = true := by decide +kernel
theorem s40_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 4 = true := by decide +kernel
theorem s40_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 5 = true := by decide +kernel
theorem s40_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 6 = true := by decide +kernel
theorem k40_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k40_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k40_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k40_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k40_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s40_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k40_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k40_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k40_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k40_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 40) ((InDA1.TCasaD 4 6 7).getD (40 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k40_6_7_12 k h.1 (by omega)
theorem col40_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 7 v) = true := by decide +kernel
theorem col40 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 40) 40 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col40_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col40_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col40_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s40_3_0
    · exact s40_3_1
    · exact s40_3_2
    · exact s40_3_3
    · exact s40_3_4
    · exact s40_3_5
    · exact s40_3_6
    · exact s40_3_7
  · fin_cases v
    · exact s40_4_0
    · exact s40_4_1
    · exact s40_4_2
    · exact s40_4_3
    · exact s40_4_4
    · exact s40_4_5
    · exact s40_4_6
    · exact s40_4_7
  · fin_cases v
    · exact s40_5_0
    · exact s40_5_1
    · exact s40_5_2
    · exact s40_5_3
    · exact s40_5_4
    · exact s40_5_5
    · exact s40_5_6
    · exact s40_5_7
  · fin_cases v
    · exact s40_6_0
    · exact s40_6_1
    · exact s40_6_2
    · exact s40_6_3
    · exact s40_6_4
    · exact s40_6_5
    · exact s40_6_6
    · exact s40_6_7
  · exact List.all_eq_true.mp col40_7 v (List.mem_finRange v)
theorem col41_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 0 v) = true := by decide +kernel
theorem col41_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 1 v) = true := by decide +kernel
theorem col41_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 2 v) = true := by decide +kernel
theorem s41_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 0 = true := by decide +kernel
theorem s41_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 1 = true := by decide +kernel
theorem s41_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 2 = true := by decide +kernel
theorem k41_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k41_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k41_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s41_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k41_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k41_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 41) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (41 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k41_3_3_26 k h.1 (by omega)
theorem s41_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 4 = true := by decide +kernel
theorem s41_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 5 = true := by decide +kernel
theorem k41_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k41_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k41_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k41_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k41_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k41_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k41_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k41_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k41_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k41_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k41_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s41_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k41_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k41_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k41_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k41_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k41_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k41_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k41_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k41_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k41_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k41_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TTsaaD 3 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k41_3_6_130 k h.1 (by omega)
theorem s41_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 3 7 = true := by decide +kernel
theorem s41_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 0 = true := by decide +kernel
theorem s41_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 1 = true := by decide +kernel
theorem s41_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 2 = true := by decide +kernel
theorem s41_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 3 = true := by decide +kernel
theorem s41_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 4 = true := by decide +kernel
theorem s41_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 5 = true := by decide +kernel
theorem k41_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k41_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k41_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k41_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k41_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k41_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k41_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s41_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k41_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k41_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k41_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k41_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k41_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k41_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 4 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k41_4_6_126 k h.1 (by omega)
theorem s41_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 4 7 = true := by decide +kernel
theorem s41_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 0 = true := by decide +kernel
theorem s41_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 1 = true := by decide +kernel
theorem s41_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 2 = true := by decide +kernel
theorem s41_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 3 = true := by decide +kernel
theorem s41_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 4 = true := by decide +kernel
theorem s41_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 5 = true := by decide +kernel
theorem k41_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k41_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k41_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k41_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k41_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k41_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k41_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s41_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k41_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k41_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k41_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k41_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k41_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k41_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 5 6).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k41_5_6_126 k h.1 (by omega)
theorem s41_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 5 7 = true := by decide +kernel
theorem s41_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 0 = true := by decide +kernel
theorem s41_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 1 = true := by decide +kernel
theorem s41_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 2 = true := by decide +kernel
theorem s41_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 3 = true := by decide +kernel
theorem s41_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 4 = true := by decide +kernel
theorem s41_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 5 = true := by decide +kernel
theorem s41_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 6 = true := by decide +kernel
theorem k41_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k41_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k41_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k41_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k41_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s41_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k41_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k41_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k41_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k41_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 41) ((InDA1.TCasaD 4 6 7).getD (41 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k41_6_7_12 k h.1 (by omega)
theorem col41_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 7 v) = true := by decide +kernel
theorem col41 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 41) 41 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col41_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col41_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col41_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s41_3_0
    · exact s41_3_1
    · exact s41_3_2
    · exact s41_3_3
    · exact s41_3_4
    · exact s41_3_5
    · exact s41_3_6
    · exact s41_3_7
  · fin_cases v
    · exact s41_4_0
    · exact s41_4_1
    · exact s41_4_2
    · exact s41_4_3
    · exact s41_4_4
    · exact s41_4_5
    · exact s41_4_6
    · exact s41_4_7
  · fin_cases v
    · exact s41_5_0
    · exact s41_5_1
    · exact s41_5_2
    · exact s41_5_3
    · exact s41_5_4
    · exact s41_5_5
    · exact s41_5_6
    · exact s41_5_7
  · fin_cases v
    · exact s41_6_0
    · exact s41_6_1
    · exact s41_6_2
    · exact s41_6_3
    · exact s41_6_4
    · exact s41_6_5
    · exact s41_6_6
    · exact s41_6_7
  · exact List.all_eq_true.mp col41_7 v (List.mem_finRange v)
theorem col42_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 0 v) = true := by decide +kernel
theorem col42_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 1 v) = true := by decide +kernel
theorem col42_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 2 v) = true := by decide +kernel
theorem s42_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 0 = true := by decide +kernel
theorem s42_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 1 = true := by decide +kernel
theorem s42_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 2 = true := by decide +kernel
theorem k42_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k42_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k42_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s42_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k42_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k42_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 42) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (42 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k42_3_3_26 k h.1 (by omega)
theorem s42_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 4 = true := by decide +kernel
theorem s42_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 5 = true := by decide +kernel
theorem k42_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k42_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k42_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k42_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k42_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k42_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k42_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k42_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k42_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k42_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k42_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s42_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k42_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k42_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k42_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k42_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k42_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k42_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k42_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k42_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k42_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k42_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TTsaaD 3 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k42_3_6_130 k h.1 (by omega)
theorem s42_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 3 7 = true := by decide +kernel
theorem s42_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 0 = true := by decide +kernel
theorem s42_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 1 = true := by decide +kernel
theorem s42_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 2 = true := by decide +kernel
theorem s42_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 3 = true := by decide +kernel
theorem s42_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 4 = true := by decide +kernel
theorem s42_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 5 = true := by decide +kernel
theorem k42_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k42_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k42_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k42_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k42_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k42_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k42_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s42_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k42_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k42_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k42_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k42_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k42_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k42_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 4 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k42_4_6_126 k h.1 (by omega)
theorem s42_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 4 7 = true := by decide +kernel
theorem s42_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 0 = true := by decide +kernel
theorem s42_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 1 = true := by decide +kernel
theorem s42_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 2 = true := by decide +kernel
theorem s42_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 3 = true := by decide +kernel
theorem s42_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 4 = true := by decide +kernel
theorem s42_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 5 = true := by decide +kernel
theorem k42_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k42_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k42_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k42_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k42_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k42_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k42_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s42_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k42_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k42_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k42_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k42_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k42_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k42_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 5 6).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k42_5_6_126 k h.1 (by omega)
theorem s42_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 5 7 = true := by decide +kernel
theorem s42_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 0 = true := by decide +kernel
theorem s42_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 1 = true := by decide +kernel
theorem s42_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 2 = true := by decide +kernel
theorem s42_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 3 = true := by decide +kernel
theorem s42_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 4 = true := by decide +kernel
theorem s42_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 5 = true := by decide +kernel
theorem s42_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 6 = true := by decide +kernel
theorem k42_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k42_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k42_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k42_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k42_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s42_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k42_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k42_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k42_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k42_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 42) ((InDA1.TCasaD 4 6 7).getD (42 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k42_6_7_12 k h.1 (by omega)
theorem col42_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 7 v) = true := by decide +kernel
theorem col42 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 42) 42 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col42_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col42_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col42_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s42_3_0
    · exact s42_3_1
    · exact s42_3_2
    · exact s42_3_3
    · exact s42_3_4
    · exact s42_3_5
    · exact s42_3_6
    · exact s42_3_7
  · fin_cases v
    · exact s42_4_0
    · exact s42_4_1
    · exact s42_4_2
    · exact s42_4_3
    · exact s42_4_4
    · exact s42_4_5
    · exact s42_4_6
    · exact s42_4_7
  · fin_cases v
    · exact s42_5_0
    · exact s42_5_1
    · exact s42_5_2
    · exact s42_5_3
    · exact s42_5_4
    · exact s42_5_5
    · exact s42_5_6
    · exact s42_5_7
  · fin_cases v
    · exact s42_6_0
    · exact s42_6_1
    · exact s42_6_2
    · exact s42_6_3
    · exact s42_6_4
    · exact s42_6_5
    · exact s42_6_6
    · exact s42_6_7
  · exact List.all_eq_true.mp col42_7 v (List.mem_finRange v)
theorem col43_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 0 v) = true := by decide +kernel
theorem col43_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 1 v) = true := by decide +kernel
theorem col43_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 2 v) = true := by decide +kernel
theorem s43_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 0 = true := by decide +kernel
theorem s43_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 1 = true := by decide +kernel
theorem s43_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 2 = true := by decide +kernel
theorem k43_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k43_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k43_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s43_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k43_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k43_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 43) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (43 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k43_3_3_26 k h.1 (by omega)
theorem s43_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 4 = true := by decide +kernel
theorem s43_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 5 = true := by decide +kernel
theorem k43_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k43_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k43_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k43_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k43_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k43_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k43_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k43_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k43_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k43_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k43_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s43_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k43_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k43_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k43_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k43_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k43_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k43_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k43_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k43_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k43_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k43_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TTsaaD 3 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k43_3_6_130 k h.1 (by omega)
theorem s43_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 3 7 = true := by decide +kernel
theorem s43_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 0 = true := by decide +kernel
theorem s43_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 1 = true := by decide +kernel
theorem s43_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 2 = true := by decide +kernel
theorem s43_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 3 = true := by decide +kernel
theorem s43_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 4 = true := by decide +kernel
theorem s43_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 5 = true := by decide +kernel
theorem k43_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k43_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k43_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k43_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k43_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k43_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k43_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s43_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k43_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k43_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k43_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k43_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k43_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k43_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 4 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k43_4_6_126 k h.1 (by omega)
theorem s43_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 4 7 = true := by decide +kernel
theorem s43_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 0 = true := by decide +kernel
theorem s43_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 1 = true := by decide +kernel
theorem s43_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 2 = true := by decide +kernel
theorem s43_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 3 = true := by decide +kernel
theorem s43_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 4 = true := by decide +kernel
theorem s43_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 5 = true := by decide +kernel
theorem k43_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k43_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k43_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k43_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k43_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k43_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k43_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s43_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k43_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k43_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k43_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k43_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k43_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k43_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 5 6).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k43_5_6_126 k h.1 (by omega)
theorem s43_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 5 7 = true := by decide +kernel
theorem s43_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 0 = true := by decide +kernel
theorem s43_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 1 = true := by decide +kernel
theorem s43_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 2 = true := by decide +kernel
theorem s43_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 3 = true := by decide +kernel
theorem s43_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 4 = true := by decide +kernel
theorem s43_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 5 = true := by decide +kernel
theorem s43_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 6 = true := by decide +kernel
theorem k43_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k43_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k43_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k43_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k43_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s43_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k43_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k43_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k43_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k43_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 43) ((InDA1.TCasaD 4 6 7).getD (43 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k43_6_7_12 k h.1 (by omega)
theorem col43_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 7 v) = true := by decide +kernel
theorem col43 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 43) 43 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col43_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col43_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col43_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s43_3_0
    · exact s43_3_1
    · exact s43_3_2
    · exact s43_3_3
    · exact s43_3_4
    · exact s43_3_5
    · exact s43_3_6
    · exact s43_3_7
  · fin_cases v
    · exact s43_4_0
    · exact s43_4_1
    · exact s43_4_2
    · exact s43_4_3
    · exact s43_4_4
    · exact s43_4_5
    · exact s43_4_6
    · exact s43_4_7
  · fin_cases v
    · exact s43_5_0
    · exact s43_5_1
    · exact s43_5_2
    · exact s43_5_3
    · exact s43_5_4
    · exact s43_5_5
    · exact s43_5_6
    · exact s43_5_7
  · fin_cases v
    · exact s43_6_0
    · exact s43_6_1
    · exact s43_6_2
    · exact s43_6_3
    · exact s43_6_4
    · exact s43_6_5
    · exact s43_6_6
    · exact s43_6_7
  · exact List.all_eq_true.mp col43_7 v (List.mem_finRange v)
theorem col44_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 0 v) = true := by decide +kernel
theorem col44_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 1 v) = true := by decide +kernel
theorem col44_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 2 v) = true := by decide +kernel
theorem s44_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 0 = true := by decide +kernel
theorem s44_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 1 = true := by decide +kernel
theorem s44_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 2 = true := by decide +kernel
theorem k44_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k44_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k44_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s44_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k44_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k44_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 44) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (44 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k44_3_3_26 k h.1 (by omega)
theorem s44_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 4 = true := by decide +kernel
theorem s44_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 5 = true := by decide +kernel
theorem k44_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k44_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k44_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k44_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k44_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k44_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k44_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k44_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k44_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k44_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k44_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s44_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k44_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k44_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k44_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k44_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k44_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k44_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k44_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k44_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k44_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k44_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TTsaaD 3 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k44_3_6_130 k h.1 (by omega)
theorem s44_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 3 7 = true := by decide +kernel
theorem s44_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 0 = true := by decide +kernel
theorem s44_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 1 = true := by decide +kernel
theorem s44_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 2 = true := by decide +kernel
theorem s44_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 3 = true := by decide +kernel
theorem s44_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 4 = true := by decide +kernel
theorem s44_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 5 = true := by decide +kernel
theorem k44_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k44_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k44_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k44_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k44_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k44_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k44_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s44_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k44_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k44_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k44_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k44_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k44_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k44_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 4 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k44_4_6_126 k h.1 (by omega)
theorem s44_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 4 7 = true := by decide +kernel
theorem s44_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 0 = true := by decide +kernel
theorem s44_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 1 = true := by decide +kernel
theorem s44_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 2 = true := by decide +kernel
theorem s44_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 3 = true := by decide +kernel
theorem s44_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 4 = true := by decide +kernel
theorem s44_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 5 = true := by decide +kernel
theorem k44_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k44_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k44_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k44_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k44_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k44_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k44_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s44_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k44_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k44_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k44_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k44_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k44_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k44_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 5 6).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k44_5_6_126 k h.1 (by omega)
theorem s44_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 5 7 = true := by decide +kernel
theorem s44_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 0 = true := by decide +kernel
theorem s44_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 1 = true := by decide +kernel
theorem s44_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 2 = true := by decide +kernel
theorem s44_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 3 = true := by decide +kernel
theorem s44_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 4 = true := by decide +kernel
theorem s44_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 5 = true := by decide +kernel
theorem s44_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 6 = true := by decide +kernel
theorem k44_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k44_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k44_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k44_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k44_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s44_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k44_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k44_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k44_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k44_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 44) ((InDA1.TCasaD 4 6 7).getD (44 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k44_6_7_12 k h.1 (by omega)
theorem col44_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 7 v) = true := by decide +kernel
theorem col44 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 44) 44 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col44_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col44_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col44_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s44_3_0
    · exact s44_3_1
    · exact s44_3_2
    · exact s44_3_3
    · exact s44_3_4
    · exact s44_3_5
    · exact s44_3_6
    · exact s44_3_7
  · fin_cases v
    · exact s44_4_0
    · exact s44_4_1
    · exact s44_4_2
    · exact s44_4_3
    · exact s44_4_4
    · exact s44_4_5
    · exact s44_4_6
    · exact s44_4_7
  · fin_cases v
    · exact s44_5_0
    · exact s44_5_1
    · exact s44_5_2
    · exact s44_5_3
    · exact s44_5_4
    · exact s44_5_5
    · exact s44_5_6
    · exact s44_5_7
  · fin_cases v
    · exact s44_6_0
    · exact s44_6_1
    · exact s44_6_2
    · exact s44_6_3
    · exact s44_6_4
    · exact s44_6_5
    · exact s44_6_6
    · exact s44_6_7
  · exact List.all_eq_true.mp col44_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
