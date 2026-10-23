module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [145, 150). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col145_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 0 v) = true := by decide +kernel
theorem col145_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 1 v) = true := by decide +kernel
theorem col145_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 2 v) = true := by decide +kernel
theorem s145_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 0 = true := by decide +kernel
theorem s145_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 1 = true := by decide +kernel
theorem s145_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 2 = true := by decide +kernel
theorem k145_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k145_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k145_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s145_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k145_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k145_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k145_3_3_26 k h.1 (by omega)
theorem s145_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 4 = true := by decide +kernel
theorem s145_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 5 = true := by decide +kernel
theorem k145_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k145_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k145_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k145_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k145_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k145_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k145_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k145_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k145_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k145_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k145_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s145_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k145_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k145_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k145_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k145_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k145_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k145_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k145_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k145_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k145_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k145_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k145_3_6_130 k h.1 (by omega)
theorem s145_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 3 7 = true := by decide +kernel
theorem s145_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 0 = true := by decide +kernel
theorem s145_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 1 = true := by decide +kernel
theorem s145_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 2 = true := by decide +kernel
theorem s145_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 3 = true := by decide +kernel
theorem s145_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 4 = true := by decide +kernel
theorem s145_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 5 = true := by decide +kernel
theorem k145_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k145_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k145_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k145_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k145_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k145_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k145_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s145_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k145_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k145_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k145_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k145_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k145_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k145_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k145_4_6_126 k h.1 (by omega)
theorem s145_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 4 7 = true := by decide +kernel
theorem s145_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 0 = true := by decide +kernel
theorem s145_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 1 = true := by decide +kernel
theorem s145_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 2 = true := by decide +kernel
theorem s145_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 3 = true := by decide +kernel
theorem s145_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 4 = true := by decide +kernel
theorem s145_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 5 = true := by decide +kernel
theorem k145_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k145_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k145_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k145_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k145_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k145_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k145_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s145_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k145_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k145_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k145_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k145_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k145_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k145_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 145) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (145 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k145_5_6_126 k h.1 (by omega)
theorem s145_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 5 7 = true := by decide +kernel
theorem s145_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 0 = true := by decide +kernel
theorem s145_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 1 = true := by decide +kernel
theorem s145_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 2 = true := by decide +kernel
theorem s145_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 3 = true := by decide +kernel
theorem s145_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 4 = true := by decide +kernel
theorem s145_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 5 = true := by decide +kernel
theorem s145_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 6 = true := by decide +kernel
theorem k145_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k145_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k145_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k145_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k145_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s145_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k145_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k145_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k145_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k145_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 145) ((InDA1.TCasaD 6 6 7).getD (145 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k145_6_7_12 k h.1 (by omega)
theorem col145_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 7 v) = true := by decide +kernel
theorem col145 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 145) 145 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col145_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col145_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col145_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s145_3_0
    · exact s145_3_1
    · exact s145_3_2
    · exact s145_3_3
    · exact s145_3_4
    · exact s145_3_5
    · exact s145_3_6
    · exact s145_3_7
  · fin_cases v
    · exact s145_4_0
    · exact s145_4_1
    · exact s145_4_2
    · exact s145_4_3
    · exact s145_4_4
    · exact s145_4_5
    · exact s145_4_6
    · exact s145_4_7
  · fin_cases v
    · exact s145_5_0
    · exact s145_5_1
    · exact s145_5_2
    · exact s145_5_3
    · exact s145_5_4
    · exact s145_5_5
    · exact s145_5_6
    · exact s145_5_7
  · fin_cases v
    · exact s145_6_0
    · exact s145_6_1
    · exact s145_6_2
    · exact s145_6_3
    · exact s145_6_4
    · exact s145_6_5
    · exact s145_6_6
    · exact s145_6_7
  · exact List.all_eq_true.mp col145_7 v (List.mem_finRange v)
theorem col146_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 0 v) = true := by decide +kernel
theorem col146_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 1 v) = true := by decide +kernel
theorem col146_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 2 v) = true := by decide +kernel
theorem s146_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 0 = true := by decide +kernel
theorem s146_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 1 = true := by decide +kernel
theorem s146_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 2 = true := by decide +kernel
theorem k146_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k146_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k146_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s146_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k146_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k146_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k146_3_3_26 k h.1 (by omega)
theorem s146_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 4 = true := by decide +kernel
theorem s146_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 5 = true := by decide +kernel
theorem k146_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k146_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k146_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k146_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k146_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k146_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k146_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k146_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k146_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k146_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k146_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s146_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k146_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k146_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k146_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k146_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k146_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k146_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k146_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k146_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k146_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k146_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k146_3_6_130 k h.1 (by omega)
theorem s146_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 3 7 = true := by decide +kernel
theorem s146_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 0 = true := by decide +kernel
theorem s146_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 1 = true := by decide +kernel
theorem s146_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 2 = true := by decide +kernel
theorem s146_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 3 = true := by decide +kernel
theorem s146_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 4 = true := by decide +kernel
theorem s146_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 5 = true := by decide +kernel
theorem k146_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k146_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k146_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k146_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k146_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k146_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k146_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s146_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k146_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k146_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k146_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k146_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k146_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k146_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k146_4_6_126 k h.1 (by omega)
theorem s146_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 4 7 = true := by decide +kernel
theorem s146_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 0 = true := by decide +kernel
theorem s146_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 1 = true := by decide +kernel
theorem s146_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 2 = true := by decide +kernel
theorem s146_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 3 = true := by decide +kernel
theorem s146_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 4 = true := by decide +kernel
theorem s146_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 5 = true := by decide +kernel
theorem k146_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k146_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k146_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k146_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k146_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k146_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k146_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s146_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k146_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k146_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k146_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k146_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k146_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k146_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 146) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (146 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k146_5_6_126 k h.1 (by omega)
theorem s146_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 5 7 = true := by decide +kernel
theorem s146_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 0 = true := by decide +kernel
theorem s146_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 1 = true := by decide +kernel
theorem s146_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 2 = true := by decide +kernel
theorem s146_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 3 = true := by decide +kernel
theorem s146_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 4 = true := by decide +kernel
theorem s146_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 5 = true := by decide +kernel
theorem s146_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 6 = true := by decide +kernel
theorem k146_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k146_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k146_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k146_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k146_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s146_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k146_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k146_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k146_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k146_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 146) ((InDA1.TCasaD 6 6 7).getD (146 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k146_6_7_12 k h.1 (by omega)
theorem col146_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 7 v) = true := by decide +kernel
theorem col146 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 146) 146 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col146_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col146_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col146_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s146_3_0
    · exact s146_3_1
    · exact s146_3_2
    · exact s146_3_3
    · exact s146_3_4
    · exact s146_3_5
    · exact s146_3_6
    · exact s146_3_7
  · fin_cases v
    · exact s146_4_0
    · exact s146_4_1
    · exact s146_4_2
    · exact s146_4_3
    · exact s146_4_4
    · exact s146_4_5
    · exact s146_4_6
    · exact s146_4_7
  · fin_cases v
    · exact s146_5_0
    · exact s146_5_1
    · exact s146_5_2
    · exact s146_5_3
    · exact s146_5_4
    · exact s146_5_5
    · exact s146_5_6
    · exact s146_5_7
  · fin_cases v
    · exact s146_6_0
    · exact s146_6_1
    · exact s146_6_2
    · exact s146_6_3
    · exact s146_6_4
    · exact s146_6_5
    · exact s146_6_6
    · exact s146_6_7
  · exact List.all_eq_true.mp col146_7 v (List.mem_finRange v)
theorem col147_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 0 v) = true := by decide +kernel
theorem col147_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 1 v) = true := by decide +kernel
theorem col147_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 2 v) = true := by decide +kernel
theorem s147_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 0 = true := by decide +kernel
theorem s147_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 1 = true := by decide +kernel
theorem s147_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 2 = true := by decide +kernel
theorem k147_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k147_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k147_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s147_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k147_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k147_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k147_3_3_26 k h.1 (by omega)
theorem s147_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 4 = true := by decide +kernel
theorem s147_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 5 = true := by decide +kernel
theorem k147_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k147_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k147_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k147_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k147_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k147_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k147_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k147_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k147_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k147_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k147_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s147_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k147_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k147_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k147_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k147_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k147_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k147_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k147_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k147_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k147_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k147_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k147_3_6_130 k h.1 (by omega)
theorem s147_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 3 7 = true := by decide +kernel
theorem s147_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 0 = true := by decide +kernel
theorem s147_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 1 = true := by decide +kernel
theorem s147_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 2 = true := by decide +kernel
theorem s147_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 3 = true := by decide +kernel
theorem s147_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 4 = true := by decide +kernel
theorem s147_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 5 = true := by decide +kernel
theorem k147_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k147_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k147_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k147_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k147_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k147_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k147_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s147_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k147_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k147_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k147_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k147_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k147_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k147_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k147_4_6_126 k h.1 (by omega)
theorem s147_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 4 7 = true := by decide +kernel
theorem s147_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 0 = true := by decide +kernel
theorem s147_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 1 = true := by decide +kernel
theorem s147_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 2 = true := by decide +kernel
theorem s147_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 3 = true := by decide +kernel
theorem s147_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 4 = true := by decide +kernel
theorem s147_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 5 = true := by decide +kernel
theorem k147_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k147_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k147_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k147_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k147_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k147_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k147_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s147_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k147_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k147_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k147_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k147_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k147_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k147_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 147) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (147 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k147_5_6_126 k h.1 (by omega)
theorem s147_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 5 7 = true := by decide +kernel
theorem s147_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 0 = true := by decide +kernel
theorem s147_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 1 = true := by decide +kernel
theorem s147_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 2 = true := by decide +kernel
theorem s147_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 3 = true := by decide +kernel
theorem s147_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 4 = true := by decide +kernel
theorem s147_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 5 = true := by decide +kernel
theorem s147_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 6 = true := by decide +kernel
theorem k147_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k147_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k147_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k147_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k147_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s147_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k147_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k147_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k147_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k147_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 147) ((InDA1.TCasaD 6 6 7).getD (147 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k147_6_7_12 k h.1 (by omega)
theorem col147_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 7 v) = true := by decide +kernel
theorem col147 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 147) 147 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col147_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col147_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col147_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s147_3_0
    · exact s147_3_1
    · exact s147_3_2
    · exact s147_3_3
    · exact s147_3_4
    · exact s147_3_5
    · exact s147_3_6
    · exact s147_3_7
  · fin_cases v
    · exact s147_4_0
    · exact s147_4_1
    · exact s147_4_2
    · exact s147_4_3
    · exact s147_4_4
    · exact s147_4_5
    · exact s147_4_6
    · exact s147_4_7
  · fin_cases v
    · exact s147_5_0
    · exact s147_5_1
    · exact s147_5_2
    · exact s147_5_3
    · exact s147_5_4
    · exact s147_5_5
    · exact s147_5_6
    · exact s147_5_7
  · fin_cases v
    · exact s147_6_0
    · exact s147_6_1
    · exact s147_6_2
    · exact s147_6_3
    · exact s147_6_4
    · exact s147_6_5
    · exact s147_6_6
    · exact s147_6_7
  · exact List.all_eq_true.mp col147_7 v (List.mem_finRange v)
theorem col148_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 0 v) = true := by decide +kernel
theorem col148_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 1 v) = true := by decide +kernel
theorem col148_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 2 v) = true := by decide +kernel
theorem s148_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 0 = true := by decide +kernel
theorem s148_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 1 = true := by decide +kernel
theorem s148_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 2 = true := by decide +kernel
theorem k148_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k148_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k148_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s148_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k148_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k148_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k148_3_3_26 k h.1 (by omega)
theorem s148_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 4 = true := by decide +kernel
theorem s148_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 5 = true := by decide +kernel
theorem k148_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k148_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k148_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k148_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k148_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k148_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k148_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k148_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k148_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k148_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k148_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s148_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k148_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k148_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k148_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k148_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k148_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k148_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k148_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k148_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k148_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k148_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k148_3_6_130 k h.1 (by omega)
theorem s148_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 3 7 = true := by decide +kernel
theorem s148_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 0 = true := by decide +kernel
theorem s148_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 1 = true := by decide +kernel
theorem s148_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 2 = true := by decide +kernel
theorem s148_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 3 = true := by decide +kernel
theorem s148_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 4 = true := by decide +kernel
theorem s148_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 5 = true := by decide +kernel
theorem k148_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k148_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k148_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k148_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k148_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k148_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k148_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s148_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k148_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k148_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k148_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k148_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k148_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k148_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k148_4_6_126 k h.1 (by omega)
theorem s148_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 4 7 = true := by decide +kernel
theorem s148_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 0 = true := by decide +kernel
theorem s148_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 1 = true := by decide +kernel
theorem s148_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 2 = true := by decide +kernel
theorem s148_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 3 = true := by decide +kernel
theorem s148_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 4 = true := by decide +kernel
theorem s148_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 5 = true := by decide +kernel
theorem k148_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k148_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k148_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k148_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k148_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k148_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k148_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s148_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k148_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k148_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k148_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k148_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k148_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k148_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 148) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (148 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k148_5_6_126 k h.1 (by omega)
theorem s148_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 5 7 = true := by decide +kernel
theorem s148_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 0 = true := by decide +kernel
theorem s148_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 1 = true := by decide +kernel
theorem s148_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 2 = true := by decide +kernel
theorem s148_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 3 = true := by decide +kernel
theorem s148_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 4 = true := by decide +kernel
theorem s148_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 5 = true := by decide +kernel
theorem s148_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 6 = true := by decide +kernel
theorem k148_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k148_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k148_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k148_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k148_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s148_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k148_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k148_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k148_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k148_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 148) ((InDA1.TCasaD 6 6 7).getD (148 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k148_6_7_12 k h.1 (by omega)
theorem col148_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 7 v) = true := by decide +kernel
theorem col148 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 148) 148 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col148_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col148_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col148_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s148_3_0
    · exact s148_3_1
    · exact s148_3_2
    · exact s148_3_3
    · exact s148_3_4
    · exact s148_3_5
    · exact s148_3_6
    · exact s148_3_7
  · fin_cases v
    · exact s148_4_0
    · exact s148_4_1
    · exact s148_4_2
    · exact s148_4_3
    · exact s148_4_4
    · exact s148_4_5
    · exact s148_4_6
    · exact s148_4_7
  · fin_cases v
    · exact s148_5_0
    · exact s148_5_1
    · exact s148_5_2
    · exact s148_5_3
    · exact s148_5_4
    · exact s148_5_5
    · exact s148_5_6
    · exact s148_5_7
  · fin_cases v
    · exact s148_6_0
    · exact s148_6_1
    · exact s148_6_2
    · exact s148_6_3
    · exact s148_6_4
    · exact s148_6_5
    · exact s148_6_6
    · exact s148_6_7
  · exact List.all_eq_true.mp col148_7 v (List.mem_finRange v)
theorem col149_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 0 v) = true := by decide +kernel
theorem col149_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 1 v) = true := by decide +kernel
theorem col149_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 2 v) = true := by decide +kernel
theorem s149_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 0 = true := by decide +kernel
theorem s149_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 1 = true := by decide +kernel
theorem s149_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 2 = true := by decide +kernel
theorem k149_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k149_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k149_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s149_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k149_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k149_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k149_3_3_26 k h.1 (by omega)
theorem s149_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 4 = true := by decide +kernel
theorem s149_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 5 = true := by decide +kernel
theorem k149_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k149_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k149_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k149_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k149_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k149_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k149_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k149_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k149_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k149_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k149_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s149_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k149_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k149_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k149_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k149_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k149_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k149_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k149_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k149_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k149_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k149_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k149_3_6_130 k h.1 (by omega)
theorem s149_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 3 7 = true := by decide +kernel
theorem s149_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 0 = true := by decide +kernel
theorem s149_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 1 = true := by decide +kernel
theorem s149_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 2 = true := by decide +kernel
theorem s149_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 3 = true := by decide +kernel
theorem s149_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 4 = true := by decide +kernel
theorem s149_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 5 = true := by decide +kernel
theorem k149_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k149_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k149_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k149_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k149_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k149_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k149_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s149_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k149_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k149_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k149_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k149_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k149_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k149_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k149_4_6_126 k h.1 (by omega)
theorem s149_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 4 7 = true := by decide +kernel
theorem s149_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 0 = true := by decide +kernel
theorem s149_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 1 = true := by decide +kernel
theorem s149_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 2 = true := by decide +kernel
theorem s149_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 3 = true := by decide +kernel
theorem s149_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 4 = true := by decide +kernel
theorem s149_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 5 = true := by decide +kernel
theorem k149_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k149_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k149_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k149_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k149_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k149_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k149_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s149_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k149_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k149_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k149_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k149_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k149_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k149_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 149) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (149 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k149_5_6_126 k h.1 (by omega)
theorem s149_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 5 7 = true := by decide +kernel
theorem s149_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 0 = true := by decide +kernel
theorem s149_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 1 = true := by decide +kernel
theorem s149_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 2 = true := by decide +kernel
theorem s149_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 3 = true := by decide +kernel
theorem s149_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 4 = true := by decide +kernel
theorem s149_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 5 = true := by decide +kernel
theorem s149_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 6 = true := by decide +kernel
theorem k149_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k149_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k149_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k149_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k149_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s149_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k149_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k149_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k149_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k149_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 149) ((InDA1.TCasaD 6 6 7).getD (149 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k149_6_7_12 k h.1 (by omega)
theorem col149_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 7 v) = true := by decide +kernel
theorem col149 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 149) 149 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col149_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col149_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col149_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s149_3_0
    · exact s149_3_1
    · exact s149_3_2
    · exact s149_3_3
    · exact s149_3_4
    · exact s149_3_5
    · exact s149_3_6
    · exact s149_3_7
  · fin_cases v
    · exact s149_4_0
    · exact s149_4_1
    · exact s149_4_2
    · exact s149_4_3
    · exact s149_4_4
    · exact s149_4_5
    · exact s149_4_6
    · exact s149_4_7
  · fin_cases v
    · exact s149_5_0
    · exact s149_5_1
    · exact s149_5_2
    · exact s149_5_3
    · exact s149_5_4
    · exact s149_5_5
    · exact s149_5_6
    · exact s149_5_7
  · fin_cases v
    · exact s149_6_0
    · exact s149_6_1
    · exact s149_6_2
    · exact s149_6_3
    · exact s149_6_4
    · exact s149_6_5
    · exact s149_6_6
    · exact s149_6_7
  · exact List.all_eq_true.mp col149_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
