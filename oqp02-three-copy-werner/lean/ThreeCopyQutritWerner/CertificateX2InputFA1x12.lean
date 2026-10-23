module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [60, 65). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col60_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 0 v) = true := by decide +kernel
theorem col60_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 1 v) = true := by decide +kernel
theorem col60_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 2 v) = true := by decide +kernel
theorem s60_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 0 = true := by decide +kernel
theorem s60_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 1 = true := by decide +kernel
theorem s60_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 2 = true := by decide +kernel
theorem k60_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k60_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k60_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s60_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k60_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k60_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 60) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (60 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k60_3_3_26 k h.1 (by omega)
theorem s60_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 4 = true := by decide +kernel
theorem s60_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 5 = true := by decide +kernel
theorem k60_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k60_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k60_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k60_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k60_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k60_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k60_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k60_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k60_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k60_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k60_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s60_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k60_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k60_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k60_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k60_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k60_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k60_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k60_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k60_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k60_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k60_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 3 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k60_3_6_130 k h.1 (by omega)
theorem s60_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 3 7 = true := by decide +kernel
theorem s60_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 0 = true := by decide +kernel
theorem s60_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 1 = true := by decide +kernel
theorem s60_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 2 = true := by decide +kernel
theorem s60_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 3 = true := by decide +kernel
theorem s60_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 4 = true := by decide +kernel
theorem s60_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 5 = true := by decide +kernel
theorem k60_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k60_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k60_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k60_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k60_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k60_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k60_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s60_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k60_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k60_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k60_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k60_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k60_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k60_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TTsaaD 4 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k60_4_6_126 k h.1 (by omega)
theorem s60_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 4 7 = true := by decide +kernel
theorem s60_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 0 = true := by decide +kernel
theorem s60_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 1 = true := by decide +kernel
theorem s60_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 2 = true := by decide +kernel
theorem s60_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 3 = true := by decide +kernel
theorem s60_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 4 = true := by decide +kernel
theorem s60_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 5 = true := by decide +kernel
theorem k60_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k60_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k60_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k60_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k60_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k60_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k60_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s60_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k60_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k60_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k60_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k60_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k60_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k60_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 5 6).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k60_5_6_126 k h.1 (by omega)
theorem s60_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 5 7 = true := by decide +kernel
theorem s60_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 0 = true := by decide +kernel
theorem s60_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 1 = true := by decide +kernel
theorem s60_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 2 = true := by decide +kernel
theorem s60_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 3 = true := by decide +kernel
theorem s60_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 4 = true := by decide +kernel
theorem s60_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 5 = true := by decide +kernel
theorem s60_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 6 = true := by decide +kernel
theorem k60_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k60_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k60_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k60_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k60_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s60_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k60_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k60_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k60_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k60_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 60) ((InDA1.TCasaD 5 6 7).getD (60 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k60_6_7_12 k h.1 (by omega)
theorem col60_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 7 v) = true := by decide +kernel
theorem col60 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 60) 60 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col60_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col60_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col60_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s60_3_0
    · exact s60_3_1
    · exact s60_3_2
    · exact s60_3_3
    · exact s60_3_4
    · exact s60_3_5
    · exact s60_3_6
    · exact s60_3_7
  · fin_cases v
    · exact s60_4_0
    · exact s60_4_1
    · exact s60_4_2
    · exact s60_4_3
    · exact s60_4_4
    · exact s60_4_5
    · exact s60_4_6
    · exact s60_4_7
  · fin_cases v
    · exact s60_5_0
    · exact s60_5_1
    · exact s60_5_2
    · exact s60_5_3
    · exact s60_5_4
    · exact s60_5_5
    · exact s60_5_6
    · exact s60_5_7
  · fin_cases v
    · exact s60_6_0
    · exact s60_6_1
    · exact s60_6_2
    · exact s60_6_3
    · exact s60_6_4
    · exact s60_6_5
    · exact s60_6_6
    · exact s60_6_7
  · exact List.all_eq_true.mp col60_7 v (List.mem_finRange v)
theorem col61_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 0 v) = true := by decide +kernel
theorem col61_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 1 v) = true := by decide +kernel
theorem col61_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 2 v) = true := by decide +kernel
theorem s61_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 0 = true := by decide +kernel
theorem s61_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 1 = true := by decide +kernel
theorem s61_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 2 = true := by decide +kernel
theorem k61_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k61_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k61_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s61_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k61_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k61_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 61) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (61 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k61_3_3_26 k h.1 (by omega)
theorem s61_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 4 = true := by decide +kernel
theorem s61_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 5 = true := by decide +kernel
theorem k61_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k61_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k61_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k61_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k61_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k61_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k61_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k61_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k61_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k61_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k61_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s61_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k61_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k61_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k61_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k61_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k61_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k61_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k61_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k61_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k61_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k61_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 3 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k61_3_6_130 k h.1 (by omega)
theorem s61_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 3 7 = true := by decide +kernel
theorem s61_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 0 = true := by decide +kernel
theorem s61_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 1 = true := by decide +kernel
theorem s61_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 2 = true := by decide +kernel
theorem s61_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 3 = true := by decide +kernel
theorem s61_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 4 = true := by decide +kernel
theorem s61_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 5 = true := by decide +kernel
theorem k61_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k61_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k61_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k61_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k61_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k61_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k61_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s61_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k61_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k61_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k61_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k61_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k61_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k61_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TTsaaD 4 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k61_4_6_126 k h.1 (by omega)
theorem s61_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 4 7 = true := by decide +kernel
theorem s61_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 0 = true := by decide +kernel
theorem s61_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 1 = true := by decide +kernel
theorem s61_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 2 = true := by decide +kernel
theorem s61_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 3 = true := by decide +kernel
theorem s61_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 4 = true := by decide +kernel
theorem s61_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 5 = true := by decide +kernel
theorem k61_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k61_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k61_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k61_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k61_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k61_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k61_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s61_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k61_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k61_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k61_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k61_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k61_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k61_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 5 6).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k61_5_6_126 k h.1 (by omega)
theorem s61_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 5 7 = true := by decide +kernel
theorem s61_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 0 = true := by decide +kernel
theorem s61_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 1 = true := by decide +kernel
theorem s61_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 2 = true := by decide +kernel
theorem s61_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 3 = true := by decide +kernel
theorem s61_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 4 = true := by decide +kernel
theorem s61_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 5 = true := by decide +kernel
theorem s61_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 6 = true := by decide +kernel
theorem k61_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k61_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k61_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k61_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k61_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s61_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k61_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k61_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k61_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k61_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 61) ((InDA1.TCasaD 5 6 7).getD (61 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k61_6_7_12 k h.1 (by omega)
theorem col61_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 7 v) = true := by decide +kernel
theorem col61 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 61) 61 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col61_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col61_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col61_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s61_3_0
    · exact s61_3_1
    · exact s61_3_2
    · exact s61_3_3
    · exact s61_3_4
    · exact s61_3_5
    · exact s61_3_6
    · exact s61_3_7
  · fin_cases v
    · exact s61_4_0
    · exact s61_4_1
    · exact s61_4_2
    · exact s61_4_3
    · exact s61_4_4
    · exact s61_4_5
    · exact s61_4_6
    · exact s61_4_7
  · fin_cases v
    · exact s61_5_0
    · exact s61_5_1
    · exact s61_5_2
    · exact s61_5_3
    · exact s61_5_4
    · exact s61_5_5
    · exact s61_5_6
    · exact s61_5_7
  · fin_cases v
    · exact s61_6_0
    · exact s61_6_1
    · exact s61_6_2
    · exact s61_6_3
    · exact s61_6_4
    · exact s61_6_5
    · exact s61_6_6
    · exact s61_6_7
  · exact List.all_eq_true.mp col61_7 v (List.mem_finRange v)
theorem col62_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 0 v) = true := by decide +kernel
theorem col62_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 1 v) = true := by decide +kernel
theorem col62_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 2 v) = true := by decide +kernel
theorem s62_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 0 = true := by decide +kernel
theorem s62_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 1 = true := by decide +kernel
theorem s62_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 2 = true := by decide +kernel
theorem k62_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k62_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k62_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s62_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k62_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k62_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 62) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (62 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k62_3_3_26 k h.1 (by omega)
theorem s62_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 4 = true := by decide +kernel
theorem s62_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 5 = true := by decide +kernel
theorem k62_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k62_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k62_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k62_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k62_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k62_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k62_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k62_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k62_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k62_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k62_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s62_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k62_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k62_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k62_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k62_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k62_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k62_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k62_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k62_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k62_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k62_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 3 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k62_3_6_130 k h.1 (by omega)
theorem s62_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 3 7 = true := by decide +kernel
theorem s62_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 0 = true := by decide +kernel
theorem s62_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 1 = true := by decide +kernel
theorem s62_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 2 = true := by decide +kernel
theorem s62_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 3 = true := by decide +kernel
theorem s62_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 4 = true := by decide +kernel
theorem s62_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 5 = true := by decide +kernel
theorem k62_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k62_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k62_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k62_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k62_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k62_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k62_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s62_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k62_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k62_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k62_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k62_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k62_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k62_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TTsaaD 4 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k62_4_6_126 k h.1 (by omega)
theorem s62_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 4 7 = true := by decide +kernel
theorem s62_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 0 = true := by decide +kernel
theorem s62_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 1 = true := by decide +kernel
theorem s62_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 2 = true := by decide +kernel
theorem s62_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 3 = true := by decide +kernel
theorem s62_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 4 = true := by decide +kernel
theorem s62_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 5 = true := by decide +kernel
theorem k62_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k62_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k62_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k62_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k62_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k62_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k62_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s62_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k62_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k62_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k62_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k62_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k62_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k62_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 5 6).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k62_5_6_126 k h.1 (by omega)
theorem s62_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 5 7 = true := by decide +kernel
theorem s62_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 0 = true := by decide +kernel
theorem s62_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 1 = true := by decide +kernel
theorem s62_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 2 = true := by decide +kernel
theorem s62_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 3 = true := by decide +kernel
theorem s62_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 4 = true := by decide +kernel
theorem s62_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 5 = true := by decide +kernel
theorem s62_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 6 = true := by decide +kernel
theorem k62_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k62_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k62_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k62_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k62_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s62_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k62_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k62_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k62_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k62_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 62) ((InDA1.TCasaD 5 6 7).getD (62 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k62_6_7_12 k h.1 (by omega)
theorem col62_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 7 v) = true := by decide +kernel
theorem col62 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 62) 62 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col62_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col62_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col62_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s62_3_0
    · exact s62_3_1
    · exact s62_3_2
    · exact s62_3_3
    · exact s62_3_4
    · exact s62_3_5
    · exact s62_3_6
    · exact s62_3_7
  · fin_cases v
    · exact s62_4_0
    · exact s62_4_1
    · exact s62_4_2
    · exact s62_4_3
    · exact s62_4_4
    · exact s62_4_5
    · exact s62_4_6
    · exact s62_4_7
  · fin_cases v
    · exact s62_5_0
    · exact s62_5_1
    · exact s62_5_2
    · exact s62_5_3
    · exact s62_5_4
    · exact s62_5_5
    · exact s62_5_6
    · exact s62_5_7
  · fin_cases v
    · exact s62_6_0
    · exact s62_6_1
    · exact s62_6_2
    · exact s62_6_3
    · exact s62_6_4
    · exact s62_6_5
    · exact s62_6_6
    · exact s62_6_7
  · exact List.all_eq_true.mp col62_7 v (List.mem_finRange v)
theorem col63_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 0 v) = true := by decide +kernel
theorem col63_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 1 v) = true := by decide +kernel
theorem col63_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 2 v) = true := by decide +kernel
theorem s63_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 0 = true := by decide +kernel
theorem s63_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 1 = true := by decide +kernel
theorem s63_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 2 = true := by decide +kernel
theorem k63_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k63_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k63_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s63_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k63_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k63_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 63) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (63 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k63_3_3_26 k h.1 (by omega)
theorem s63_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 4 = true := by decide +kernel
theorem s63_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 5 = true := by decide +kernel
theorem k63_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k63_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k63_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k63_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k63_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k63_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k63_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k63_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k63_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k63_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k63_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s63_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k63_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k63_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k63_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k63_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k63_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k63_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k63_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k63_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k63_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k63_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 3 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k63_3_6_130 k h.1 (by omega)
theorem s63_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 3 7 = true := by decide +kernel
theorem s63_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 0 = true := by decide +kernel
theorem s63_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 1 = true := by decide +kernel
theorem s63_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 2 = true := by decide +kernel
theorem s63_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 3 = true := by decide +kernel
theorem s63_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 4 = true := by decide +kernel
theorem s63_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 5 = true := by decide +kernel
theorem k63_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k63_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k63_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k63_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k63_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k63_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k63_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s63_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k63_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k63_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k63_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k63_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k63_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k63_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TTsaaD 4 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k63_4_6_126 k h.1 (by omega)
theorem s63_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 4 7 = true := by decide +kernel
theorem s63_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 0 = true := by decide +kernel
theorem s63_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 1 = true := by decide +kernel
theorem s63_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 2 = true := by decide +kernel
theorem s63_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 3 = true := by decide +kernel
theorem s63_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 4 = true := by decide +kernel
theorem s63_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 5 = true := by decide +kernel
theorem k63_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k63_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k63_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k63_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k63_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k63_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k63_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s63_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k63_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k63_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k63_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k63_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k63_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k63_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 5 6).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k63_5_6_126 k h.1 (by omega)
theorem s63_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 5 7 = true := by decide +kernel
theorem s63_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 0 = true := by decide +kernel
theorem s63_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 1 = true := by decide +kernel
theorem s63_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 2 = true := by decide +kernel
theorem s63_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 3 = true := by decide +kernel
theorem s63_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 4 = true := by decide +kernel
theorem s63_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 5 = true := by decide +kernel
theorem s63_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 6 = true := by decide +kernel
theorem k63_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k63_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k63_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k63_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k63_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s63_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k63_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k63_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k63_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k63_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 63) ((InDA1.TCasaD 5 6 7).getD (63 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k63_6_7_12 k h.1 (by omega)
theorem col63_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 7 v) = true := by decide +kernel
theorem col63 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 63) 63 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col63_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col63_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col63_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s63_3_0
    · exact s63_3_1
    · exact s63_3_2
    · exact s63_3_3
    · exact s63_3_4
    · exact s63_3_5
    · exact s63_3_6
    · exact s63_3_7
  · fin_cases v
    · exact s63_4_0
    · exact s63_4_1
    · exact s63_4_2
    · exact s63_4_3
    · exact s63_4_4
    · exact s63_4_5
    · exact s63_4_6
    · exact s63_4_7
  · fin_cases v
    · exact s63_5_0
    · exact s63_5_1
    · exact s63_5_2
    · exact s63_5_3
    · exact s63_5_4
    · exact s63_5_5
    · exact s63_5_6
    · exact s63_5_7
  · fin_cases v
    · exact s63_6_0
    · exact s63_6_1
    · exact s63_6_2
    · exact s63_6_3
    · exact s63_6_4
    · exact s63_6_5
    · exact s63_6_6
    · exact s63_6_7
  · exact List.all_eq_true.mp col63_7 v (List.mem_finRange v)
theorem col64_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 0 v) = true := by decide +kernel
theorem col64_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 1 v) = true := by decide +kernel
theorem col64_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 2 v) = true := by decide +kernel
theorem s64_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 0 = true := by decide +kernel
theorem s64_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 1 = true := by decide +kernel
theorem s64_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 2 = true := by decide +kernel
theorem k64_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k64_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k64_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s64_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k64_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k64_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 64) (InDA1.TCasaD 3 3 5) (posA (x2Mult 1 5) (64 - x2AOff 1 5)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k64_3_3_26 k h.1 (by omega)
theorem s64_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 4 = true := by decide +kernel
theorem s64_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 5 = true := by decide +kernel
theorem k64_3_6_0 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k64_3_6_13 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k64_3_6_26 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k64_3_6_39 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k64_3_6_52 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k64_3_6_65 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k64_3_6_78 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k64_3_6_91 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k64_3_6_104 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k64_3_6_117 : (List.range 13).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k64_3_6_130 : (List.range 6).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s64_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k64_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k64_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k64_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k64_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k64_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k64_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k64_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k64_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k64_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k64_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 3 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k64_3_6_130 k h.1 (by omega)
theorem s64_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 3 7 = true := by decide +kernel
theorem s64_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 0 = true := by decide +kernel
theorem s64_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 1 = true := by decide +kernel
theorem s64_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 2 = true := by decide +kernel
theorem s64_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 3 = true := by decide +kernel
theorem s64_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 4 = true := by decide +kernel
theorem s64_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 5 = true := by decide +kernel
theorem k64_4_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k64_4_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k64_4_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k64_4_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k64_4_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k64_4_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k64_4_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s64_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 6 = true := by
  rw [segOKA_gPT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k64_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k64_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k64_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k64_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k64_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k64_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TTsaaD 4 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k64_4_6_126 k h.1 (by omega)
theorem s64_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 4 7 = true := by decide +kernel
theorem s64_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 0 = true := by decide +kernel
theorem s64_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 1 = true := by decide +kernel
theorem s64_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 2 = true := by decide +kernel
theorem s64_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 3 = true := by decide +kernel
theorem s64_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 4 = true := by decide +kernel
theorem s64_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 5 = true := by decide +kernel
theorem k64_5_6_0 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k64_5_6_21 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k64_5_6_42 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k64_5_6_63 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k64_5_6_84 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k64_5_6_105 : (List.range 21).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k64_5_6_126 : (List.range 10).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s64_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 6 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k64_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k64_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k64_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k64_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k64_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k64_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 5 6).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k64_5_6_126 k h.1 (by omega)
theorem s64_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 5 7 = true := by decide +kernel
theorem s64_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 0 = true := by decide +kernel
theorem s64_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 1 = true := by decide +kernel
theorem s64_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 2 = true := by decide +kernel
theorem s64_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 3 = true := by decide +kernel
theorem s64_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 4 = true := by decide +kernel
theorem s64_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 5 = true := by decide +kernel
theorem s64_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 6 = true := by decide +kernel
theorem k64_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k64_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k64_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k64_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k64_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s64_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k64_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k64_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k64_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k64_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 64) ((InDA1.TCasaD 5 6 7).getD (64 - x2AOff 1 5) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k64_6_7_12 k h.1 (by omega)
theorem col64_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 7 v) = true := by decide +kernel
theorem col64 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 64) 64 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col64_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col64_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col64_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s64_3_0
    · exact s64_3_1
    · exact s64_3_2
    · exact s64_3_3
    · exact s64_3_4
    · exact s64_3_5
    · exact s64_3_6
    · exact s64_3_7
  · fin_cases v
    · exact s64_4_0
    · exact s64_4_1
    · exact s64_4_2
    · exact s64_4_3
    · exact s64_4_4
    · exact s64_4_5
    · exact s64_4_6
    · exact s64_4_7
  · fin_cases v
    · exact s64_5_0
    · exact s64_5_1
    · exact s64_5_2
    · exact s64_5_3
    · exact s64_5_4
    · exact s64_5_5
    · exact s64_5_6
    · exact s64_5_7
  · fin_cases v
    · exact s64_6_0
    · exact s64_6_1
    · exact s64_6_2
    · exact s64_6_3
    · exact s64_6_4
    · exact s64_6_5
    · exact s64_6_6
    · exact s64_6_7
  · exact List.all_eq_true.mp col64_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
