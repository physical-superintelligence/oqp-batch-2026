module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [70, 75). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col70_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 0 v) = true := by decide +kernel
theorem col70_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 1 v) = true := by decide +kernel
theorem col70_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 2 v) = true := by decide +kernel
theorem s70_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 0 = true := by decide +kernel
theorem s70_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 1 = true := by decide +kernel
theorem s70_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 2 = true := by decide +kernel
theorem k70_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k70_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k70_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s70_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k70_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k70_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 70) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (70 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k70_3_3_26 k h.1 (by omega)
theorem s70_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 4 = true := by decide +kernel
theorem s70_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 5 = true := by decide +kernel
theorem k70_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k70_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k70_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k70_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k70_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k70_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k70_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k70_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k70_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k70_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k70_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s70_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k70_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k70_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k70_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k70_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k70_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k70_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k70_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k70_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k70_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k70_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 3 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k70_3_6_130 k h.1 (by omega)
theorem s70_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 3 7 = true := by decide +kernel
theorem s70_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 0 = true := by decide +kernel
theorem s70_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 1 = true := by decide +kernel
theorem s70_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 2 = true := by decide +kernel
theorem s70_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 3 = true := by decide +kernel
theorem s70_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 4 = true := by decide +kernel
theorem s70_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 5 = true := by decide +kernel
theorem k70_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k70_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k70_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k70_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k70_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k70_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k70_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s70_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k70_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k70_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k70_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k70_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k70_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k70_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TTsaaD 4 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k70_4_6_126 k h.1 (by omega)
theorem s70_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 4 7 = true := by decide +kernel
theorem s70_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 0 = true := by decide +kernel
theorem s70_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 1 = true := by decide +kernel
theorem s70_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 2 = true := by decide +kernel
theorem s70_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 3 = true := by decide +kernel
theorem s70_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 4 = true := by decide +kernel
theorem s70_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 5 = true := by decide +kernel
theorem k70_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k70_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k70_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k70_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k70_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k70_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k70_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s70_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k70_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k70_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k70_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k70_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k70_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k70_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 5 6).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k70_5_6_126 k h.1 (by omega)
theorem s70_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 5 7 = true := by decide +kernel
theorem s70_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 0 = true := by decide +kernel
theorem s70_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 1 = true := by decide +kernel
theorem s70_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 2 = true := by decide +kernel
theorem s70_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 3 = true := by decide +kernel
theorem s70_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 4 = true := by decide +kernel
theorem s70_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 5 = true := by decide +kernel
theorem s70_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 6 = true := by decide +kernel
theorem k70_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k70_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k70_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k70_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k70_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s70_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k70_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k70_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k70_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k70_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 70) ((InDA1.TCasaD 5 6 7).getD (70 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k70_6_7_12 k h.1 (by omega)
theorem col70_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 7 v) = true := by decide +kernel
theorem col70 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 70) 70 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col70_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col70_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col70_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s70_3_0
    · exact s70_3_1
    · exact s70_3_2
    · exact s70_3_3
    · exact s70_3_4
    · exact s70_3_5
    · exact s70_3_6
    · exact s70_3_7
  · fin_cases v
    · exact s70_4_0
    · exact s70_4_1
    · exact s70_4_2
    · exact s70_4_3
    · exact s70_4_4
    · exact s70_4_5
    · exact s70_4_6
    · exact s70_4_7
  · fin_cases v
    · exact s70_5_0
    · exact s70_5_1
    · exact s70_5_2
    · exact s70_5_3
    · exact s70_5_4
    · exact s70_5_5
    · exact s70_5_6
    · exact s70_5_7
  · fin_cases v
    · exact s70_6_0
    · exact s70_6_1
    · exact s70_6_2
    · exact s70_6_3
    · exact s70_6_4
    · exact s70_6_5
    · exact s70_6_6
    · exact s70_6_7
  · exact List.all_eq_true.mp col70_7 v (List.mem_finRange v)
theorem col71_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 0 v) = true := by decide +kernel
theorem col71_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 1 v) = true := by decide +kernel
theorem col71_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 2 v) = true := by decide +kernel
theorem s71_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 0 = true := by decide +kernel
theorem s71_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 1 = true := by decide +kernel
theorem s71_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 2 = true := by decide +kernel
theorem k71_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k71_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k71_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s71_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k71_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k71_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 71) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (71 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k71_3_3_26 k h.1 (by omega)
theorem s71_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 4 = true := by decide +kernel
theorem s71_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 5 = true := by decide +kernel
theorem k71_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k71_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k71_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k71_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k71_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k71_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k71_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k71_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k71_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k71_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k71_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s71_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k71_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k71_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k71_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k71_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k71_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k71_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k71_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k71_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k71_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k71_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 3 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k71_3_6_130 k h.1 (by omega)
theorem s71_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 3 7 = true := by decide +kernel
theorem s71_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 0 = true := by decide +kernel
theorem s71_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 1 = true := by decide +kernel
theorem s71_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 2 = true := by decide +kernel
theorem s71_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 3 = true := by decide +kernel
theorem s71_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 4 = true := by decide +kernel
theorem s71_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 5 = true := by decide +kernel
theorem k71_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k71_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k71_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k71_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k71_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k71_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k71_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s71_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k71_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k71_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k71_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k71_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k71_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k71_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TTsaaD 4 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k71_4_6_126 k h.1 (by omega)
theorem s71_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 4 7 = true := by decide +kernel
theorem s71_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 0 = true := by decide +kernel
theorem s71_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 1 = true := by decide +kernel
theorem s71_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 2 = true := by decide +kernel
theorem s71_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 3 = true := by decide +kernel
theorem s71_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 4 = true := by decide +kernel
theorem s71_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 5 = true := by decide +kernel
theorem k71_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k71_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k71_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k71_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k71_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k71_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k71_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s71_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k71_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k71_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k71_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k71_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k71_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k71_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 5 6).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k71_5_6_126 k h.1 (by omega)
theorem s71_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 5 7 = true := by decide +kernel
theorem s71_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 0 = true := by decide +kernel
theorem s71_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 1 = true := by decide +kernel
theorem s71_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 2 = true := by decide +kernel
theorem s71_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 3 = true := by decide +kernel
theorem s71_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 4 = true := by decide +kernel
theorem s71_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 5 = true := by decide +kernel
theorem s71_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 6 = true := by decide +kernel
theorem k71_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k71_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k71_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k71_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k71_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s71_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k71_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k71_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k71_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k71_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 71) ((InDA1.TCasaD 5 6 7).getD (71 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k71_6_7_12 k h.1 (by omega)
theorem col71_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 7 v) = true := by decide +kernel
theorem col71 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 71) 71 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col71_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col71_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col71_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s71_3_0
    · exact s71_3_1
    · exact s71_3_2
    · exact s71_3_3
    · exact s71_3_4
    · exact s71_3_5
    · exact s71_3_6
    · exact s71_3_7
  · fin_cases v
    · exact s71_4_0
    · exact s71_4_1
    · exact s71_4_2
    · exact s71_4_3
    · exact s71_4_4
    · exact s71_4_5
    · exact s71_4_6
    · exact s71_4_7
  · fin_cases v
    · exact s71_5_0
    · exact s71_5_1
    · exact s71_5_2
    · exact s71_5_3
    · exact s71_5_4
    · exact s71_5_5
    · exact s71_5_6
    · exact s71_5_7
  · fin_cases v
    · exact s71_6_0
    · exact s71_6_1
    · exact s71_6_2
    · exact s71_6_3
    · exact s71_6_4
    · exact s71_6_5
    · exact s71_6_6
    · exact s71_6_7
  · exact List.all_eq_true.mp col71_7 v (List.mem_finRange v)
theorem col72_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 0 v) = true := by decide +kernel
theorem col72_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 1 v) = true := by decide +kernel
theorem col72_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 2 v) = true := by decide +kernel
theorem s72_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 0 = true := by decide +kernel
theorem s72_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 1 = true := by decide +kernel
theorem s72_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 2 = true := by decide +kernel
theorem k72_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k72_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k72_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s72_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k72_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k72_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 72) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (72 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k72_3_3_26 k h.1 (by omega)
theorem s72_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 4 = true := by decide +kernel
theorem s72_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 5 = true := by decide +kernel
theorem k72_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k72_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k72_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k72_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k72_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k72_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k72_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k72_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k72_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k72_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k72_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s72_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k72_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k72_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k72_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k72_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k72_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k72_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k72_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k72_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k72_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k72_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 3 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k72_3_6_130 k h.1 (by omega)
theorem s72_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 3 7 = true := by decide +kernel
theorem s72_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 0 = true := by decide +kernel
theorem s72_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 1 = true := by decide +kernel
theorem s72_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 2 = true := by decide +kernel
theorem s72_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 3 = true := by decide +kernel
theorem s72_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 4 = true := by decide +kernel
theorem s72_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 5 = true := by decide +kernel
theorem k72_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k72_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k72_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k72_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k72_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k72_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k72_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s72_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k72_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k72_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k72_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k72_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k72_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k72_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TTsaaD 4 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k72_4_6_126 k h.1 (by omega)
theorem s72_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 4 7 = true := by decide +kernel
theorem s72_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 0 = true := by decide +kernel
theorem s72_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 1 = true := by decide +kernel
theorem s72_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 2 = true := by decide +kernel
theorem s72_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 3 = true := by decide +kernel
theorem s72_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 4 = true := by decide +kernel
theorem s72_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 5 = true := by decide +kernel
theorem k72_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k72_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k72_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k72_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k72_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k72_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k72_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s72_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k72_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k72_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k72_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k72_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k72_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k72_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 5 6).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k72_5_6_126 k h.1 (by omega)
theorem s72_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 5 7 = true := by decide +kernel
theorem s72_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 0 = true := by decide +kernel
theorem s72_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 1 = true := by decide +kernel
theorem s72_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 2 = true := by decide +kernel
theorem s72_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 3 = true := by decide +kernel
theorem s72_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 4 = true := by decide +kernel
theorem s72_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 5 = true := by decide +kernel
theorem s72_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 6 = true := by decide +kernel
theorem k72_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k72_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k72_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k72_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k72_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s72_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k72_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k72_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k72_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k72_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 72) ((InDA1.TCasaD 5 6 7).getD (72 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k72_6_7_12 k h.1 (by omega)
theorem col72_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 7 v) = true := by decide +kernel
theorem col72 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 72) 72 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col72_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col72_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col72_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s72_3_0
    · exact s72_3_1
    · exact s72_3_2
    · exact s72_3_3
    · exact s72_3_4
    · exact s72_3_5
    · exact s72_3_6
    · exact s72_3_7
  · fin_cases v
    · exact s72_4_0
    · exact s72_4_1
    · exact s72_4_2
    · exact s72_4_3
    · exact s72_4_4
    · exact s72_4_5
    · exact s72_4_6
    · exact s72_4_7
  · fin_cases v
    · exact s72_5_0
    · exact s72_5_1
    · exact s72_5_2
    · exact s72_5_3
    · exact s72_5_4
    · exact s72_5_5
    · exact s72_5_6
    · exact s72_5_7
  · fin_cases v
    · exact s72_6_0
    · exact s72_6_1
    · exact s72_6_2
    · exact s72_6_3
    · exact s72_6_4
    · exact s72_6_5
    · exact s72_6_6
    · exact s72_6_7
  · exact List.all_eq_true.mp col72_7 v (List.mem_finRange v)
theorem col73_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 0 v) = true := by decide +kernel
theorem col73_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 1 v) = true := by decide +kernel
theorem col73_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 2 v) = true := by decide +kernel
theorem s73_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 0 = true := by decide +kernel
theorem s73_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 1 = true := by decide +kernel
theorem s73_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 2 = true := by decide +kernel
theorem k73_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k73_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k73_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s73_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k73_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k73_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 73) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (73 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k73_3_3_26 k h.1 (by omega)
theorem s73_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 4 = true := by decide +kernel
theorem s73_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 5 = true := by decide +kernel
theorem k73_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k73_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k73_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k73_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k73_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k73_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k73_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k73_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k73_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k73_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k73_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s73_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k73_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k73_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k73_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k73_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k73_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k73_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k73_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k73_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k73_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k73_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 3 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k73_3_6_130 k h.1 (by omega)
theorem s73_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 3 7 = true := by decide +kernel
theorem s73_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 0 = true := by decide +kernel
theorem s73_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 1 = true := by decide +kernel
theorem s73_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 2 = true := by decide +kernel
theorem s73_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 3 = true := by decide +kernel
theorem s73_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 4 = true := by decide +kernel
theorem s73_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 5 = true := by decide +kernel
theorem k73_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k73_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k73_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k73_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k73_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k73_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k73_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s73_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k73_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k73_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k73_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k73_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k73_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k73_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TTsaaD 4 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k73_4_6_126 k h.1 (by omega)
theorem s73_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 4 7 = true := by decide +kernel
theorem s73_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 0 = true := by decide +kernel
theorem s73_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 1 = true := by decide +kernel
theorem s73_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 2 = true := by decide +kernel
theorem s73_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 3 = true := by decide +kernel
theorem s73_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 4 = true := by decide +kernel
theorem s73_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 5 = true := by decide +kernel
theorem k73_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k73_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k73_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k73_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k73_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k73_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k73_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s73_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k73_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k73_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k73_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k73_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k73_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k73_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 5 6).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k73_5_6_126 k h.1 (by omega)
theorem s73_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 5 7 = true := by decide +kernel
theorem s73_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 0 = true := by decide +kernel
theorem s73_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 1 = true := by decide +kernel
theorem s73_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 2 = true := by decide +kernel
theorem s73_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 3 = true := by decide +kernel
theorem s73_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 4 = true := by decide +kernel
theorem s73_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 5 = true := by decide +kernel
theorem s73_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 6 = true := by decide +kernel
theorem k73_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k73_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k73_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k73_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k73_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s73_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k73_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k73_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k73_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k73_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 73) ((InDA1.TCasaD 5 6 7).getD (73 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k73_6_7_12 k h.1 (by omega)
theorem col73_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 7 v) = true := by decide +kernel
theorem col73 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 73) 73 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col73_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col73_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col73_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s73_3_0
    · exact s73_3_1
    · exact s73_3_2
    · exact s73_3_3
    · exact s73_3_4
    · exact s73_3_5
    · exact s73_3_6
    · exact s73_3_7
  · fin_cases v
    · exact s73_4_0
    · exact s73_4_1
    · exact s73_4_2
    · exact s73_4_3
    · exact s73_4_4
    · exact s73_4_5
    · exact s73_4_6
    · exact s73_4_7
  · fin_cases v
    · exact s73_5_0
    · exact s73_5_1
    · exact s73_5_2
    · exact s73_5_3
    · exact s73_5_4
    · exact s73_5_5
    · exact s73_5_6
    · exact s73_5_7
  · fin_cases v
    · exact s73_6_0
    · exact s73_6_1
    · exact s73_6_2
    · exact s73_6_3
    · exact s73_6_4
    · exact s73_6_5
    · exact s73_6_6
    · exact s73_6_7
  · exact List.all_eq_true.mp col73_7 v (List.mem_finRange v)
theorem col74_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 0 v) = true := by decide +kernel
theorem col74_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 1 v) = true := by decide +kernel
theorem col74_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 2 v) = true := by decide +kernel
theorem s74_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 0 = true := by decide +kernel
theorem s74_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 1 = true := by decide +kernel
theorem s74_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 2 = true := by decide +kernel
theorem k74_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k74_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k74_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s74_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k74_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k74_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 74) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (74 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k74_3_3_26 k h.1 (by omega)
theorem s74_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 4 = true := by decide +kernel
theorem s74_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 5 = true := by decide +kernel
theorem k74_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k74_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k74_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k74_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k74_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k74_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k74_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k74_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k74_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k74_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k74_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s74_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k74_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k74_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k74_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k74_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k74_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k74_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k74_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k74_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k74_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k74_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 3 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k74_3_6_130 k h.1 (by omega)
theorem s74_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 3 7 = true := by decide +kernel
theorem s74_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 0 = true := by decide +kernel
theorem s74_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 1 = true := by decide +kernel
theorem s74_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 2 = true := by decide +kernel
theorem s74_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 3 = true := by decide +kernel
theorem s74_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 4 = true := by decide +kernel
theorem s74_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 5 = true := by decide +kernel
theorem k74_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k74_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k74_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k74_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k74_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k74_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k74_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s74_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k74_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k74_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k74_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k74_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k74_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k74_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TTsaaD 4 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k74_4_6_126 k h.1 (by omega)
theorem s74_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 4 7 = true := by decide +kernel
theorem s74_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 0 = true := by decide +kernel
theorem s74_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 1 = true := by decide +kernel
theorem s74_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 2 = true := by decide +kernel
theorem s74_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 3 = true := by decide +kernel
theorem s74_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 4 = true := by decide +kernel
theorem s74_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 5 = true := by decide +kernel
theorem k74_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k74_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k74_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k74_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k74_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k74_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k74_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s74_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k74_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k74_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k74_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k74_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k74_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k74_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 5 6).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k74_5_6_126 k h.1 (by omega)
theorem s74_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 5 7 = true := by decide +kernel
theorem s74_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 0 = true := by decide +kernel
theorem s74_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 1 = true := by decide +kernel
theorem s74_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 2 = true := by decide +kernel
theorem s74_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 3 = true := by decide +kernel
theorem s74_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 4 = true := by decide +kernel
theorem s74_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 5 = true := by decide +kernel
theorem s74_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 6 = true := by decide +kernel
theorem k74_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k74_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k74_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k74_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k74_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s74_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k74_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k74_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k74_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k74_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 74) ((InDA1.TCasaD 5 6 7).getD (74 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k74_6_7_12 k h.1 (by omega)
theorem col74_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 7 v) = true := by decide +kernel
theorem col74 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 74) 74 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col74_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col74_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col74_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s74_3_0
    · exact s74_3_1
    · exact s74_3_2
    · exact s74_3_3
    · exact s74_3_4
    · exact s74_3_5
    · exact s74_3_6
    · exact s74_3_7
  · fin_cases v
    · exact s74_4_0
    · exact s74_4_1
    · exact s74_4_2
    · exact s74_4_3
    · exact s74_4_4
    · exact s74_4_5
    · exact s74_4_6
    · exact s74_4_7
  · fin_cases v
    · exact s74_5_0
    · exact s74_5_1
    · exact s74_5_2
    · exact s74_5_3
    · exact s74_5_4
    · exact s74_5_5
    · exact s74_5_6
    · exact s74_5_7
  · fin_cases v
    · exact s74_6_0
    · exact s74_6_1
    · exact s74_6_2
    · exact s74_6_3
    · exact s74_6_4
    · exact s74_6_5
    · exact s74_6_6
    · exact s74_6_7
  · exact List.all_eq_true.mp col74_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
