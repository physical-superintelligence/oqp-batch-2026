module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [45, 50). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col45_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 0 v) = true := by decide +kernel
theorem col45_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 1 v) = true := by decide +kernel
theorem col45_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 2 v) = true := by decide +kernel
theorem s45_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 0 = true := by decide +kernel
theorem s45_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 1 = true := by decide +kernel
theorem s45_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 2 = true := by decide +kernel
theorem k45_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k45_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k45_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s45_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k45_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k45_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 45) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (45 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k45_3_3_26 k h.1 (by omega)
theorem s45_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 4 = true := by decide +kernel
theorem s45_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 5 = true := by decide +kernel
theorem k45_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k45_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k45_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k45_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k45_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k45_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k45_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k45_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k45_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k45_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k45_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s45_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k45_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k45_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k45_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k45_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k45_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k45_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k45_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k45_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k45_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k45_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TTsaaD 3 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k45_3_6_130 k h.1 (by omega)
theorem s45_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 3 7 = true := by decide +kernel
theorem s45_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 0 = true := by decide +kernel
theorem s45_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 1 = true := by decide +kernel
theorem s45_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 2 = true := by decide +kernel
theorem s45_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 3 = true := by decide +kernel
theorem s45_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 4 = true := by decide +kernel
theorem s45_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 5 = true := by decide +kernel
theorem k45_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k45_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k45_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k45_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k45_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k45_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k45_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s45_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k45_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k45_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k45_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k45_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k45_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k45_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 4 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k45_4_6_126 k h.1 (by omega)
theorem s45_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 4 7 = true := by decide +kernel
theorem s45_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 0 = true := by decide +kernel
theorem s45_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 1 = true := by decide +kernel
theorem s45_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 2 = true := by decide +kernel
theorem s45_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 3 = true := by decide +kernel
theorem s45_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 4 = true := by decide +kernel
theorem s45_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 5 = true := by decide +kernel
theorem k45_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k45_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k45_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k45_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k45_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k45_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k45_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s45_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k45_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k45_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k45_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k45_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k45_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k45_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 5 6).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k45_5_6_126 k h.1 (by omega)
theorem s45_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 5 7 = true := by decide +kernel
theorem s45_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 0 = true := by decide +kernel
theorem s45_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 1 = true := by decide +kernel
theorem s45_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 2 = true := by decide +kernel
theorem s45_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 3 = true := by decide +kernel
theorem s45_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 4 = true := by decide +kernel
theorem s45_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 5 = true := by decide +kernel
theorem s45_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 6 = true := by decide +kernel
theorem k45_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k45_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k45_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k45_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k45_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s45_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k45_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k45_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k45_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k45_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 45) ((InDA1.TCasaD 4 6 7).getD (45 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k45_6_7_12 k h.1 (by omega)
theorem col45_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 7 v) = true := by decide +kernel
theorem col45 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 45) 45 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col45_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col45_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col45_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s45_3_0
    · exact s45_3_1
    · exact s45_3_2
    · exact s45_3_3
    · exact s45_3_4
    · exact s45_3_5
    · exact s45_3_6
    · exact s45_3_7
  · fin_cases v
    · exact s45_4_0
    · exact s45_4_1
    · exact s45_4_2
    · exact s45_4_3
    · exact s45_4_4
    · exact s45_4_5
    · exact s45_4_6
    · exact s45_4_7
  · fin_cases v
    · exact s45_5_0
    · exact s45_5_1
    · exact s45_5_2
    · exact s45_5_3
    · exact s45_5_4
    · exact s45_5_5
    · exact s45_5_6
    · exact s45_5_7
  · fin_cases v
    · exact s45_6_0
    · exact s45_6_1
    · exact s45_6_2
    · exact s45_6_3
    · exact s45_6_4
    · exact s45_6_5
    · exact s45_6_6
    · exact s45_6_7
  · exact List.all_eq_true.mp col45_7 v (List.mem_finRange v)
theorem col46_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 0 v) = true := by decide +kernel
theorem col46_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 1 v) = true := by decide +kernel
theorem col46_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 2 v) = true := by decide +kernel
theorem s46_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 0 = true := by decide +kernel
theorem s46_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 1 = true := by decide +kernel
theorem s46_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 2 = true := by decide +kernel
theorem k46_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k46_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k46_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s46_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k46_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k46_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 46) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (46 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k46_3_3_26 k h.1 (by omega)
theorem s46_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 4 = true := by decide +kernel
theorem s46_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 5 = true := by decide +kernel
theorem k46_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k46_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k46_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k46_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k46_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k46_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k46_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k46_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k46_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k46_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k46_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s46_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k46_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k46_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k46_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k46_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k46_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k46_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k46_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k46_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k46_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k46_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TTsaaD 3 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k46_3_6_130 k h.1 (by omega)
theorem s46_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 3 7 = true := by decide +kernel
theorem s46_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 0 = true := by decide +kernel
theorem s46_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 1 = true := by decide +kernel
theorem s46_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 2 = true := by decide +kernel
theorem s46_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 3 = true := by decide +kernel
theorem s46_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 4 = true := by decide +kernel
theorem s46_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 5 = true := by decide +kernel
theorem k46_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k46_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k46_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k46_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k46_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k46_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k46_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s46_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k46_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k46_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k46_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k46_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k46_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k46_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 4 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k46_4_6_126 k h.1 (by omega)
theorem s46_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 4 7 = true := by decide +kernel
theorem s46_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 0 = true := by decide +kernel
theorem s46_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 1 = true := by decide +kernel
theorem s46_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 2 = true := by decide +kernel
theorem s46_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 3 = true := by decide +kernel
theorem s46_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 4 = true := by decide +kernel
theorem s46_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 5 = true := by decide +kernel
theorem k46_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k46_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k46_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k46_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k46_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k46_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k46_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s46_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k46_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k46_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k46_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k46_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k46_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k46_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 5 6).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k46_5_6_126 k h.1 (by omega)
theorem s46_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 5 7 = true := by decide +kernel
theorem s46_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 0 = true := by decide +kernel
theorem s46_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 1 = true := by decide +kernel
theorem s46_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 2 = true := by decide +kernel
theorem s46_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 3 = true := by decide +kernel
theorem s46_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 4 = true := by decide +kernel
theorem s46_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 5 = true := by decide +kernel
theorem s46_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 6 = true := by decide +kernel
theorem k46_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k46_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k46_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k46_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k46_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s46_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k46_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k46_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k46_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k46_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 46) ((InDA1.TCasaD 4 6 7).getD (46 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k46_6_7_12 k h.1 (by omega)
theorem col46_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 7 v) = true := by decide +kernel
theorem col46 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 46) 46 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col46_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col46_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col46_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s46_3_0
    · exact s46_3_1
    · exact s46_3_2
    · exact s46_3_3
    · exact s46_3_4
    · exact s46_3_5
    · exact s46_3_6
    · exact s46_3_7
  · fin_cases v
    · exact s46_4_0
    · exact s46_4_1
    · exact s46_4_2
    · exact s46_4_3
    · exact s46_4_4
    · exact s46_4_5
    · exact s46_4_6
    · exact s46_4_7
  · fin_cases v
    · exact s46_5_0
    · exact s46_5_1
    · exact s46_5_2
    · exact s46_5_3
    · exact s46_5_4
    · exact s46_5_5
    · exact s46_5_6
    · exact s46_5_7
  · fin_cases v
    · exact s46_6_0
    · exact s46_6_1
    · exact s46_6_2
    · exact s46_6_3
    · exact s46_6_4
    · exact s46_6_5
    · exact s46_6_6
    · exact s46_6_7
  · exact List.all_eq_true.mp col46_7 v (List.mem_finRange v)
theorem col47_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 0 v) = true := by decide +kernel
theorem col47_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 1 v) = true := by decide +kernel
theorem col47_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 2 v) = true := by decide +kernel
theorem s47_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 0 = true := by decide +kernel
theorem s47_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 1 = true := by decide +kernel
theorem s47_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 2 = true := by decide +kernel
theorem k47_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k47_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k47_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s47_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k47_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k47_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 47) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (47 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k47_3_3_26 k h.1 (by omega)
theorem s47_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 4 = true := by decide +kernel
theorem s47_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 5 = true := by decide +kernel
theorem k47_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k47_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k47_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k47_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k47_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k47_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k47_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k47_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k47_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k47_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k47_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s47_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k47_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k47_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k47_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k47_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k47_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k47_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k47_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k47_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k47_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k47_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TTsaaD 3 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k47_3_6_130 k h.1 (by omega)
theorem s47_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 3 7 = true := by decide +kernel
theorem s47_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 0 = true := by decide +kernel
theorem s47_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 1 = true := by decide +kernel
theorem s47_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 2 = true := by decide +kernel
theorem s47_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 3 = true := by decide +kernel
theorem s47_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 4 = true := by decide +kernel
theorem s47_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 5 = true := by decide +kernel
theorem k47_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k47_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k47_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k47_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k47_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k47_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k47_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s47_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k47_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k47_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k47_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k47_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k47_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k47_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 4 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k47_4_6_126 k h.1 (by omega)
theorem s47_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 4 7 = true := by decide +kernel
theorem s47_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 0 = true := by decide +kernel
theorem s47_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 1 = true := by decide +kernel
theorem s47_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 2 = true := by decide +kernel
theorem s47_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 3 = true := by decide +kernel
theorem s47_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 4 = true := by decide +kernel
theorem s47_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 5 = true := by decide +kernel
theorem k47_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k47_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k47_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k47_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k47_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k47_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k47_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s47_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k47_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k47_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k47_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k47_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k47_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k47_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 5 6).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k47_5_6_126 k h.1 (by omega)
theorem s47_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 5 7 = true := by decide +kernel
theorem s47_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 0 = true := by decide +kernel
theorem s47_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 1 = true := by decide +kernel
theorem s47_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 2 = true := by decide +kernel
theorem s47_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 3 = true := by decide +kernel
theorem s47_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 4 = true := by decide +kernel
theorem s47_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 5 = true := by decide +kernel
theorem s47_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 6 = true := by decide +kernel
theorem k47_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k47_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k47_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k47_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k47_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s47_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k47_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k47_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k47_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k47_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 47) ((InDA1.TCasaD 4 6 7).getD (47 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k47_6_7_12 k h.1 (by omega)
theorem col47_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 7 v) = true := by decide +kernel
theorem col47 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 47) 47 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col47_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col47_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col47_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s47_3_0
    · exact s47_3_1
    · exact s47_3_2
    · exact s47_3_3
    · exact s47_3_4
    · exact s47_3_5
    · exact s47_3_6
    · exact s47_3_7
  · fin_cases v
    · exact s47_4_0
    · exact s47_4_1
    · exact s47_4_2
    · exact s47_4_3
    · exact s47_4_4
    · exact s47_4_5
    · exact s47_4_6
    · exact s47_4_7
  · fin_cases v
    · exact s47_5_0
    · exact s47_5_1
    · exact s47_5_2
    · exact s47_5_3
    · exact s47_5_4
    · exact s47_5_5
    · exact s47_5_6
    · exact s47_5_7
  · fin_cases v
    · exact s47_6_0
    · exact s47_6_1
    · exact s47_6_2
    · exact s47_6_3
    · exact s47_6_4
    · exact s47_6_5
    · exact s47_6_6
    · exact s47_6_7
  · exact List.all_eq_true.mp col47_7 v (List.mem_finRange v)
theorem col48_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 0 v) = true := by decide +kernel
theorem col48_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 1 v) = true := by decide +kernel
theorem col48_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 2 v) = true := by decide +kernel
theorem s48_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 0 = true := by decide +kernel
theorem s48_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 1 = true := by decide +kernel
theorem s48_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 2 = true := by decide +kernel
theorem k48_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k48_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k48_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s48_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k48_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k48_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 48) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (48 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k48_3_3_26 k h.1 (by omega)
theorem s48_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 4 = true := by decide +kernel
theorem s48_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 5 = true := by decide +kernel
theorem k48_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k48_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k48_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k48_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k48_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k48_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k48_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k48_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k48_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k48_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k48_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s48_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k48_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k48_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k48_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k48_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k48_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k48_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k48_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k48_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k48_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k48_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TTsaaD 3 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k48_3_6_130 k h.1 (by omega)
theorem s48_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 3 7 = true := by decide +kernel
theorem s48_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 0 = true := by decide +kernel
theorem s48_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 1 = true := by decide +kernel
theorem s48_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 2 = true := by decide +kernel
theorem s48_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 3 = true := by decide +kernel
theorem s48_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 4 = true := by decide +kernel
theorem s48_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 5 = true := by decide +kernel
theorem k48_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k48_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k48_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k48_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k48_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k48_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k48_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s48_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k48_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k48_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k48_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k48_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k48_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k48_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 4 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k48_4_6_126 k h.1 (by omega)
theorem s48_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 4 7 = true := by decide +kernel
theorem s48_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 0 = true := by decide +kernel
theorem s48_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 1 = true := by decide +kernel
theorem s48_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 2 = true := by decide +kernel
theorem s48_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 3 = true := by decide +kernel
theorem s48_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 4 = true := by decide +kernel
theorem s48_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 5 = true := by decide +kernel
theorem k48_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k48_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k48_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k48_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k48_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k48_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k48_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s48_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k48_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k48_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k48_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k48_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k48_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k48_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 5 6).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k48_5_6_126 k h.1 (by omega)
theorem s48_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 5 7 = true := by decide +kernel
theorem s48_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 0 = true := by decide +kernel
theorem s48_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 1 = true := by decide +kernel
theorem s48_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 2 = true := by decide +kernel
theorem s48_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 3 = true := by decide +kernel
theorem s48_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 4 = true := by decide +kernel
theorem s48_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 5 = true := by decide +kernel
theorem s48_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 6 = true := by decide +kernel
theorem k48_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k48_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k48_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k48_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k48_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s48_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k48_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k48_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k48_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k48_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 48) ((InDA1.TCasaD 4 6 7).getD (48 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k48_6_7_12 k h.1 (by omega)
theorem col48_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 7 v) = true := by decide +kernel
theorem col48 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 48) 48 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col48_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col48_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col48_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s48_3_0
    · exact s48_3_1
    · exact s48_3_2
    · exact s48_3_3
    · exact s48_3_4
    · exact s48_3_5
    · exact s48_3_6
    · exact s48_3_7
  · fin_cases v
    · exact s48_4_0
    · exact s48_4_1
    · exact s48_4_2
    · exact s48_4_3
    · exact s48_4_4
    · exact s48_4_5
    · exact s48_4_6
    · exact s48_4_7
  · fin_cases v
    · exact s48_5_0
    · exact s48_5_1
    · exact s48_5_2
    · exact s48_5_3
    · exact s48_5_4
    · exact s48_5_5
    · exact s48_5_6
    · exact s48_5_7
  · fin_cases v
    · exact s48_6_0
    · exact s48_6_1
    · exact s48_6_2
    · exact s48_6_3
    · exact s48_6_4
    · exact s48_6_5
    · exact s48_6_6
    · exact s48_6_7
  · exact List.all_eq_true.mp col48_7 v (List.mem_finRange v)
theorem col49_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 0 v) = true := by decide +kernel
theorem col49_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 1 v) = true := by decide +kernel
theorem col49_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 2 v) = true := by decide +kernel
theorem s49_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 0 = true := by decide +kernel
theorem s49_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 1 = true := by decide +kernel
theorem s49_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 2 = true := by decide +kernel
theorem k49_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k49_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k49_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s49_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k49_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k49_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 49) (InDA1.TCasaD 3 3 4) (posA (x2Mult 1 4) (49 - x2AOff 1 4)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k49_3_3_26 k h.1 (by omega)
theorem s49_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 4 = true := by decide +kernel
theorem s49_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 5 = true := by decide +kernel
theorem k49_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k49_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k49_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k49_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k49_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k49_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k49_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k49_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k49_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k49_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k49_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s49_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k49_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k49_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k49_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k49_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k49_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k49_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k49_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k49_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k49_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k49_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TTsaaD 3 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k49_3_6_130 k h.1 (by omega)
theorem s49_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 3 7 = true := by decide +kernel
theorem s49_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 0 = true := by decide +kernel
theorem s49_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 1 = true := by decide +kernel
theorem s49_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 2 = true := by decide +kernel
theorem s49_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 3 = true := by decide +kernel
theorem s49_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 4 = true := by decide +kernel
theorem s49_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 5 = true := by decide +kernel
theorem k49_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k49_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k49_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k49_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k49_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k49_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k49_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s49_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k49_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k49_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k49_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k49_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k49_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k49_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 4 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k49_4_6_126 k h.1 (by omega)
theorem s49_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 4 7 = true := by decide +kernel
theorem s49_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 0 = true := by decide +kernel
theorem s49_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 1 = true := by decide +kernel
theorem s49_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 2 = true := by decide +kernel
theorem s49_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 3 = true := by decide +kernel
theorem s49_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 4 = true := by decide +kernel
theorem s49_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 5 = true := by decide +kernel
theorem k49_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k49_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k49_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k49_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k49_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k49_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k49_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s49_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k49_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k49_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k49_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k49_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k49_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k49_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 5 6).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k49_5_6_126 k h.1 (by omega)
theorem s49_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 5 7 = true := by decide +kernel
theorem s49_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 0 = true := by decide +kernel
theorem s49_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 1 = true := by decide +kernel
theorem s49_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 2 = true := by decide +kernel
theorem s49_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 3 = true := by decide +kernel
theorem s49_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 4 = true := by decide +kernel
theorem s49_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 5 = true := by decide +kernel
theorem s49_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 6 = true := by decide +kernel
theorem k49_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k49_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k49_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k49_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k49_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s49_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k49_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k49_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k49_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k49_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 49) ((InDA1.TCasaD 4 6 7).getD (49 - x2AOff 1 4) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k49_6_7_12 k h.1 (by omega)
theorem col49_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 7 v) = true := by decide +kernel
theorem col49 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 49) 49 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col49_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col49_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col49_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s49_3_0
    · exact s49_3_1
    · exact s49_3_2
    · exact s49_3_3
    · exact s49_3_4
    · exact s49_3_5
    · exact s49_3_6
    · exact s49_3_7
  · fin_cases v
    · exact s49_4_0
    · exact s49_4_1
    · exact s49_4_2
    · exact s49_4_3
    · exact s49_4_4
    · exact s49_4_5
    · exact s49_4_6
    · exact s49_4_7
  · fin_cases v
    · exact s49_5_0
    · exact s49_5_1
    · exact s49_5_2
    · exact s49_5_3
    · exact s49_5_4
    · exact s49_5_5
    · exact s49_5_6
    · exact s49_5_7
  · fin_cases v
    · exact s49_6_0
    · exact s49_6_1
    · exact s49_6_2
    · exact s49_6_3
    · exact s49_6_4
    · exact s49_6_5
    · exact s49_6_6
    · exact s49_6_7
  · exact List.all_eq_true.mp col49_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
