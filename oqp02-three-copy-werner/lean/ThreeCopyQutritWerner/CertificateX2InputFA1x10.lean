module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [50, 55). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col50_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 0 v) = true := by decide +kernel
theorem col50_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 1 v) = true := by decide +kernel
theorem col50_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 2 v) = true := by decide +kernel
theorem s50_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 0 = true := by decide +kernel
theorem s50_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 1 = true := by decide +kernel
theorem s50_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 2 = true := by decide +kernel
theorem k50_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k50_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k50_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s50_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k50_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k50_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 50) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (50 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k50_3_3_26 k h.1 (by omega)
theorem s50_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 4 = true := by decide +kernel
theorem s50_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 5 = true := by decide +kernel
theorem k50_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k50_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k50_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k50_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k50_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k50_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k50_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k50_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k50_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k50_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k50_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s50_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k50_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k50_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k50_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k50_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k50_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k50_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k50_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k50_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k50_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k50_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TTsaaD 3 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k50_3_6_130 k h.1 (by omega)
theorem s50_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 3 7 = true := by decide +kernel
theorem s50_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 0 = true := by decide +kernel
theorem s50_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 1 = true := by decide +kernel
theorem s50_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 2 = true := by decide +kernel
theorem s50_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 3 = true := by decide +kernel
theorem s50_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 4 = true := by decide +kernel
theorem s50_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 5 = true := by decide +kernel
theorem k50_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k50_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k50_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k50_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k50_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k50_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k50_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s50_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k50_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k50_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k50_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k50_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k50_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k50_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 4 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k50_4_6_126 k h.1 (by omega)
theorem s50_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 4 7 = true := by decide +kernel
theorem s50_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 0 = true := by decide +kernel
theorem s50_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 1 = true := by decide +kernel
theorem s50_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 2 = true := by decide +kernel
theorem s50_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 3 = true := by decide +kernel
theorem s50_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 4 = true := by decide +kernel
theorem s50_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 5 = true := by decide +kernel
theorem k50_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k50_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k50_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k50_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k50_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k50_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k50_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s50_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k50_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k50_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k50_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k50_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k50_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k50_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 5 6).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k50_5_6_126 k h.1 (by omega)
theorem s50_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 5 7 = true := by decide +kernel
theorem s50_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 0 = true := by decide +kernel
theorem s50_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 1 = true := by decide +kernel
theorem s50_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 2 = true := by decide +kernel
theorem s50_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 3 = true := by decide +kernel
theorem s50_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 4 = true := by decide +kernel
theorem s50_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 5 = true := by decide +kernel
theorem s50_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 6 = true := by decide +kernel
theorem k50_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k50_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k50_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k50_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k50_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s50_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k50_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k50_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k50_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k50_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 50) ((InDA1.TCasaD 4 6 7).getD (50 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k50_6_7_12 k h.1 (by omega)
theorem col50_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 7 v) = true := by decide +kernel
theorem col50 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 50) 50 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col50_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col50_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col50_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s50_3_0
    · exact s50_3_1
    · exact s50_3_2
    · exact s50_3_3
    · exact s50_3_4
    · exact s50_3_5
    · exact s50_3_6
    · exact s50_3_7
  · fin_cases v
    · exact s50_4_0
    · exact s50_4_1
    · exact s50_4_2
    · exact s50_4_3
    · exact s50_4_4
    · exact s50_4_5
    · exact s50_4_6
    · exact s50_4_7
  · fin_cases v
    · exact s50_5_0
    · exact s50_5_1
    · exact s50_5_2
    · exact s50_5_3
    · exact s50_5_4
    · exact s50_5_5
    · exact s50_5_6
    · exact s50_5_7
  · fin_cases v
    · exact s50_6_0
    · exact s50_6_1
    · exact s50_6_2
    · exact s50_6_3
    · exact s50_6_4
    · exact s50_6_5
    · exact s50_6_6
    · exact s50_6_7
  · exact List.all_eq_true.mp col50_7 v (List.mem_finRange v)
theorem col51_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 0 v) = true := by decide +kernel
theorem col51_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 1 v) = true := by decide +kernel
theorem col51_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 2 v) = true := by decide +kernel
theorem s51_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 0 = true := by decide +kernel
theorem s51_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 1 = true := by decide +kernel
theorem s51_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 2 = true := by decide +kernel
theorem k51_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k51_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k51_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s51_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k51_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k51_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 51) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (51 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k51_3_3_26 k h.1 (by omega)
theorem s51_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 4 = true := by decide +kernel
theorem s51_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 5 = true := by decide +kernel
theorem k51_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k51_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k51_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k51_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k51_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k51_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k51_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k51_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k51_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k51_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k51_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s51_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k51_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k51_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k51_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k51_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k51_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k51_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k51_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k51_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k51_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k51_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TTsaaD 3 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k51_3_6_130 k h.1 (by omega)
theorem s51_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 3 7 = true := by decide +kernel
theorem s51_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 0 = true := by decide +kernel
theorem s51_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 1 = true := by decide +kernel
theorem s51_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 2 = true := by decide +kernel
theorem s51_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 3 = true := by decide +kernel
theorem s51_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 4 = true := by decide +kernel
theorem s51_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 5 = true := by decide +kernel
theorem k51_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k51_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k51_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k51_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k51_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k51_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k51_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s51_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k51_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k51_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k51_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k51_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k51_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k51_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 4 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k51_4_6_126 k h.1 (by omega)
theorem s51_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 4 7 = true := by decide +kernel
theorem s51_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 0 = true := by decide +kernel
theorem s51_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 1 = true := by decide +kernel
theorem s51_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 2 = true := by decide +kernel
theorem s51_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 3 = true := by decide +kernel
theorem s51_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 4 = true := by decide +kernel
theorem s51_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 5 = true := by decide +kernel
theorem k51_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k51_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k51_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k51_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k51_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k51_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k51_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s51_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k51_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k51_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k51_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k51_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k51_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k51_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 5 6).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k51_5_6_126 k h.1 (by omega)
theorem s51_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 5 7 = true := by decide +kernel
theorem s51_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 0 = true := by decide +kernel
theorem s51_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 1 = true := by decide +kernel
theorem s51_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 2 = true := by decide +kernel
theorem s51_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 3 = true := by decide +kernel
theorem s51_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 4 = true := by decide +kernel
theorem s51_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 5 = true := by decide +kernel
theorem s51_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 6 = true := by decide +kernel
theorem k51_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k51_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k51_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k51_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k51_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s51_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k51_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k51_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k51_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k51_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 51) ((InDA1.TCasaD 4 6 7).getD (51 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k51_6_7_12 k h.1 (by omega)
theorem col51_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 7 v) = true := by decide +kernel
theorem col51 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 51) 51 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col51_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col51_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col51_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s51_3_0
    · exact s51_3_1
    · exact s51_3_2
    · exact s51_3_3
    · exact s51_3_4
    · exact s51_3_5
    · exact s51_3_6
    · exact s51_3_7
  · fin_cases v
    · exact s51_4_0
    · exact s51_4_1
    · exact s51_4_2
    · exact s51_4_3
    · exact s51_4_4
    · exact s51_4_5
    · exact s51_4_6
    · exact s51_4_7
  · fin_cases v
    · exact s51_5_0
    · exact s51_5_1
    · exact s51_5_2
    · exact s51_5_3
    · exact s51_5_4
    · exact s51_5_5
    · exact s51_5_6
    · exact s51_5_7
  · fin_cases v
    · exact s51_6_0
    · exact s51_6_1
    · exact s51_6_2
    · exact s51_6_3
    · exact s51_6_4
    · exact s51_6_5
    · exact s51_6_6
    · exact s51_6_7
  · exact List.all_eq_true.mp col51_7 v (List.mem_finRange v)
theorem col52_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 0 v) = true := by decide +kernel
theorem col52_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 1 v) = true := by decide +kernel
theorem col52_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 2 v) = true := by decide +kernel
theorem s52_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 0 = true := by decide +kernel
theorem s52_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 1 = true := by decide +kernel
theorem s52_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 2 = true := by decide +kernel
theorem k52_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k52_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k52_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s52_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k52_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k52_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 52) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (52 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k52_3_3_26 k h.1 (by omega)
theorem s52_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 4 = true := by decide +kernel
theorem s52_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 5 = true := by decide +kernel
theorem k52_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k52_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k52_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k52_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k52_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k52_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k52_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k52_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k52_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k52_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k52_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s52_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k52_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k52_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k52_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k52_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k52_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k52_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k52_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k52_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k52_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k52_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TTsaaD 3 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k52_3_6_130 k h.1 (by omega)
theorem s52_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 3 7 = true := by decide +kernel
theorem s52_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 0 = true := by decide +kernel
theorem s52_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 1 = true := by decide +kernel
theorem s52_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 2 = true := by decide +kernel
theorem s52_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 3 = true := by decide +kernel
theorem s52_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 4 = true := by decide +kernel
theorem s52_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 5 = true := by decide +kernel
theorem k52_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k52_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k52_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k52_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k52_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k52_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k52_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s52_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k52_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k52_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k52_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k52_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k52_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k52_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 4 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k52_4_6_126 k h.1 (by omega)
theorem s52_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 4 7 = true := by decide +kernel
theorem s52_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 0 = true := by decide +kernel
theorem s52_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 1 = true := by decide +kernel
theorem s52_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 2 = true := by decide +kernel
theorem s52_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 3 = true := by decide +kernel
theorem s52_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 4 = true := by decide +kernel
theorem s52_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 5 = true := by decide +kernel
theorem k52_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k52_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k52_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k52_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k52_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k52_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k52_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s52_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k52_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k52_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k52_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k52_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k52_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k52_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 5 6).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k52_5_6_126 k h.1 (by omega)
theorem s52_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 5 7 = true := by decide +kernel
theorem s52_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 0 = true := by decide +kernel
theorem s52_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 1 = true := by decide +kernel
theorem s52_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 2 = true := by decide +kernel
theorem s52_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 3 = true := by decide +kernel
theorem s52_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 4 = true := by decide +kernel
theorem s52_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 5 = true := by decide +kernel
theorem s52_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 6 = true := by decide +kernel
theorem k52_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k52_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k52_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k52_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k52_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s52_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k52_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k52_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k52_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k52_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 52) ((InDA1.TCasaD 4 6 7).getD (52 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k52_6_7_12 k h.1 (by omega)
theorem col52_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 7 v) = true := by decide +kernel
theorem col52 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 52) 52 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col52_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col52_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col52_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s52_3_0
    · exact s52_3_1
    · exact s52_3_2
    · exact s52_3_3
    · exact s52_3_4
    · exact s52_3_5
    · exact s52_3_6
    · exact s52_3_7
  · fin_cases v
    · exact s52_4_0
    · exact s52_4_1
    · exact s52_4_2
    · exact s52_4_3
    · exact s52_4_4
    · exact s52_4_5
    · exact s52_4_6
    · exact s52_4_7
  · fin_cases v
    · exact s52_5_0
    · exact s52_5_1
    · exact s52_5_2
    · exact s52_5_3
    · exact s52_5_4
    · exact s52_5_5
    · exact s52_5_6
    · exact s52_5_7
  · fin_cases v
    · exact s52_6_0
    · exact s52_6_1
    · exact s52_6_2
    · exact s52_6_3
    · exact s52_6_4
    · exact s52_6_5
    · exact s52_6_6
    · exact s52_6_7
  · exact List.all_eq_true.mp col52_7 v (List.mem_finRange v)
theorem col53_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 0 v) = true := by decide +kernel
theorem col53_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 1 v) = true := by decide +kernel
theorem col53_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 2 v) = true := by decide +kernel
theorem s53_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 0 = true := by decide +kernel
theorem s53_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 1 = true := by decide +kernel
theorem s53_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 2 = true := by decide +kernel
theorem k53_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k53_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k53_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s53_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k53_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k53_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 53) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (53 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k53_3_3_26 k h.1 (by omega)
theorem s53_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 4 = true := by decide +kernel
theorem s53_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 5 = true := by decide +kernel
theorem k53_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k53_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k53_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k53_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k53_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k53_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k53_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k53_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k53_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k53_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k53_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s53_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k53_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k53_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k53_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k53_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k53_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k53_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k53_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k53_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k53_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k53_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TTsaaD 3 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k53_3_6_130 k h.1 (by omega)
theorem s53_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 3 7 = true := by decide +kernel
theorem s53_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 0 = true := by decide +kernel
theorem s53_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 1 = true := by decide +kernel
theorem s53_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 2 = true := by decide +kernel
theorem s53_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 3 = true := by decide +kernel
theorem s53_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 4 = true := by decide +kernel
theorem s53_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 5 = true := by decide +kernel
theorem k53_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k53_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k53_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k53_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k53_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k53_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k53_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s53_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k53_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k53_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k53_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k53_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k53_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k53_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 4 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k53_4_6_126 k h.1 (by omega)
theorem s53_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 4 7 = true := by decide +kernel
theorem s53_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 0 = true := by decide +kernel
theorem s53_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 1 = true := by decide +kernel
theorem s53_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 2 = true := by decide +kernel
theorem s53_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 3 = true := by decide +kernel
theorem s53_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 4 = true := by decide +kernel
theorem s53_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 5 = true := by decide +kernel
theorem k53_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k53_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k53_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k53_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k53_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k53_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k53_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s53_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k53_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k53_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k53_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k53_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k53_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k53_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 5 6).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k53_5_6_126 k h.1 (by omega)
theorem s53_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 5 7 = true := by decide +kernel
theorem s53_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 0 = true := by decide +kernel
theorem s53_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 1 = true := by decide +kernel
theorem s53_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 2 = true := by decide +kernel
theorem s53_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 3 = true := by decide +kernel
theorem s53_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 4 = true := by decide +kernel
theorem s53_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 5 = true := by decide +kernel
theorem s53_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 6 = true := by decide +kernel
theorem k53_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k53_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k53_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k53_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k53_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s53_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k53_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k53_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k53_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k53_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 53) ((InDA1.TCasaD 4 6 7).getD (53 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k53_6_7_12 k h.1 (by omega)
theorem col53_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 7 v) = true := by decide +kernel
theorem col53 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 53) 53 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col53_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col53_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col53_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s53_3_0
    · exact s53_3_1
    · exact s53_3_2
    · exact s53_3_3
    · exact s53_3_4
    · exact s53_3_5
    · exact s53_3_6
    · exact s53_3_7
  · fin_cases v
    · exact s53_4_0
    · exact s53_4_1
    · exact s53_4_2
    · exact s53_4_3
    · exact s53_4_4
    · exact s53_4_5
    · exact s53_4_6
    · exact s53_4_7
  · fin_cases v
    · exact s53_5_0
    · exact s53_5_1
    · exact s53_5_2
    · exact s53_5_3
    · exact s53_5_4
    · exact s53_5_5
    · exact s53_5_6
    · exact s53_5_7
  · fin_cases v
    · exact s53_6_0
    · exact s53_6_1
    · exact s53_6_2
    · exact s53_6_3
    · exact s53_6_4
    · exact s53_6_5
    · exact s53_6_6
    · exact s53_6_7
  · exact List.all_eq_true.mp col53_7 v (List.mem_finRange v)
theorem col54_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 0 v) = true := by decide +kernel
theorem col54_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 1 v) = true := by decide +kernel
theorem col54_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 2 v) = true := by decide +kernel
theorem s54_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 0 = true := by decide +kernel
theorem s54_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 1 = true := by decide +kernel
theorem s54_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 2 = true := by decide +kernel
theorem k54_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k54_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k54_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s54_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k54_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k54_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 54) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (54 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k54_3_3_26 k h.1 (by omega)
theorem s54_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 4 = true := by decide +kernel
theorem s54_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 5 = true := by decide +kernel
theorem k54_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k54_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k54_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k54_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k54_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k54_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k54_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k54_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k54_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k54_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k54_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s54_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k54_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k54_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k54_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k54_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k54_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k54_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k54_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k54_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k54_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k54_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TTsaaD 3 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k54_3_6_130 k h.1 (by omega)
theorem s54_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 3 7 = true := by decide +kernel
theorem s54_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 0 = true := by decide +kernel
theorem s54_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 1 = true := by decide +kernel
theorem s54_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 2 = true := by decide +kernel
theorem s54_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 3 = true := by decide +kernel
theorem s54_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 4 = true := by decide +kernel
theorem s54_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 5 = true := by decide +kernel
theorem k54_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k54_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k54_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k54_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k54_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k54_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k54_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s54_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k54_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k54_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k54_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k54_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k54_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k54_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 4 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k54_4_6_126 k h.1 (by omega)
theorem s54_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 4 7 = true := by decide +kernel
theorem s54_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 0 = true := by decide +kernel
theorem s54_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 1 = true := by decide +kernel
theorem s54_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 2 = true := by decide +kernel
theorem s54_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 3 = true := by decide +kernel
theorem s54_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 4 = true := by decide +kernel
theorem s54_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 5 = true := by decide +kernel
theorem k54_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k54_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k54_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k54_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k54_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k54_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k54_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s54_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k54_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k54_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k54_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k54_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k54_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k54_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 5 6).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k54_5_6_126 k h.1 (by omega)
theorem s54_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 5 7 = true := by decide +kernel
theorem s54_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 0 = true := by decide +kernel
theorem s54_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 1 = true := by decide +kernel
theorem s54_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 2 = true := by decide +kernel
theorem s54_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 3 = true := by decide +kernel
theorem s54_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 4 = true := by decide +kernel
theorem s54_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 5 = true := by decide +kernel
theorem s54_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 6 = true := by decide +kernel
theorem k54_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k54_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k54_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k54_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k54_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s54_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k54_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k54_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k54_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k54_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 54) ((InDA1.TCasaD 4 6 7).getD (54 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k54_6_7_12 k h.1 (by omega)
theorem col54_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 7 v) = true := by decide +kernel
theorem col54 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 54) 54 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col54_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col54_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col54_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s54_3_0
    · exact s54_3_1
    · exact s54_3_2
    · exact s54_3_3
    · exact s54_3_4
    · exact s54_3_5
    · exact s54_3_6
    · exact s54_3_7
  · fin_cases v
    · exact s54_4_0
    · exact s54_4_1
    · exact s54_4_2
    · exact s54_4_3
    · exact s54_4_4
    · exact s54_4_5
    · exact s54_4_6
    · exact s54_4_7
  · fin_cases v
    · exact s54_5_0
    · exact s54_5_1
    · exact s54_5_2
    · exact s54_5_3
    · exact s54_5_4
    · exact s54_5_5
    · exact s54_5_6
    · exact s54_5_7
  · fin_cases v
    · exact s54_6_0
    · exact s54_6_1
    · exact s54_6_2
    · exact s54_6_3
    · exact s54_6_4
    · exact s54_6_5
    · exact s54_6_6
    · exact s54_6_7
  · exact List.all_eq_true.mp col54_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
