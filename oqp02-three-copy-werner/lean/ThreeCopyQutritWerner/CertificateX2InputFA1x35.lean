module

public import ThreeCopyQutritWerner.CertificateX2InputDA1
public import ThreeCopyQutritWerner.CertificateX2CoreA1gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A1g input table, columns [175, 180). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col175_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 0 v) = true := by decide +kernel
theorem col175_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 1 v) = true := by decide +kernel
theorem col175_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 2 v) = true := by decide +kernel
theorem s175_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 0 = true := by decide +kernel
theorem s175_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 1 = true := by decide +kernel
theorem s175_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 2 = true := by decide +kernel
theorem k175_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k175_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k175_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s175_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k175_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k175_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k175_3_3_26 k h.1 (by omega)
theorem s175_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 4 = true := by decide +kernel
theorem s175_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 5 = true := by decide +kernel
theorem k175_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k175_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k175_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k175_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k175_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k175_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k175_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k175_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k175_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k175_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k175_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s175_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k175_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k175_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k175_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k175_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k175_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k175_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k175_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k175_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k175_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k175_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k175_3_6_130 k h.1 (by omega)
theorem s175_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 3 7 = true := by decide +kernel
theorem s175_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 0 = true := by decide +kernel
theorem s175_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 1 = true := by decide +kernel
theorem s175_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 2 = true := by decide +kernel
theorem s175_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 3 = true := by decide +kernel
theorem s175_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 4 = true := by decide +kernel
theorem s175_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 5 = true := by decide +kernel
theorem k175_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k175_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k175_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k175_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k175_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k175_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k175_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s175_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k175_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k175_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k175_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k175_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k175_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k175_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k175_4_6_126 k h.1 (by omega)
theorem s175_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 4 7 = true := by decide +kernel
theorem s175_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 0 = true := by decide +kernel
theorem s175_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 1 = true := by decide +kernel
theorem s175_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 2 = true := by decide +kernel
theorem s175_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 3 = true := by decide +kernel
theorem s175_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 4 = true := by decide +kernel
theorem s175_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 5 = true := by decide +kernel
theorem k175_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k175_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k175_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k175_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k175_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k175_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k175_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s175_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k175_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k175_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k175_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k175_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k175_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k175_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 175) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (175 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k175_5_6_126 k h.1 (by omega)
theorem s175_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 5 7 = true := by decide +kernel
theorem s175_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 0 = true := by decide +kernel
theorem s175_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 1 = true := by decide +kernel
theorem s175_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 2 = true := by decide +kernel
theorem s175_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 3 = true := by decide +kernel
theorem s175_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 4 = true := by decide +kernel
theorem s175_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 5 = true := by decide +kernel
theorem s175_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 6 = true := by decide +kernel
theorem k175_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k175_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k175_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k175_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k175_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s175_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k175_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k175_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k175_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k175_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 175) ((InDA1.TCasaD 6 6 7).getD (175 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k175_6_7_12 k h.1 (by omega)
theorem col175_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 7 v) = true := by decide +kernel
theorem col175 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 175) 175 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col175_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col175_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col175_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s175_3_0
    · exact s175_3_1
    · exact s175_3_2
    · exact s175_3_3
    · exact s175_3_4
    · exact s175_3_5
    · exact s175_3_6
    · exact s175_3_7
  · fin_cases v
    · exact s175_4_0
    · exact s175_4_1
    · exact s175_4_2
    · exact s175_4_3
    · exact s175_4_4
    · exact s175_4_5
    · exact s175_4_6
    · exact s175_4_7
  · fin_cases v
    · exact s175_5_0
    · exact s175_5_1
    · exact s175_5_2
    · exact s175_5_3
    · exact s175_5_4
    · exact s175_5_5
    · exact s175_5_6
    · exact s175_5_7
  · fin_cases v
    · exact s175_6_0
    · exact s175_6_1
    · exact s175_6_2
    · exact s175_6_3
    · exact s175_6_4
    · exact s175_6_5
    · exact s175_6_6
    · exact s175_6_7
  · exact List.all_eq_true.mp col175_7 v (List.mem_finRange v)
theorem col176_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 0 v) = true := by decide +kernel
theorem col176_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 1 v) = true := by decide +kernel
theorem col176_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 2 v) = true := by decide +kernel
theorem s176_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 0 = true := by decide +kernel
theorem s176_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 1 = true := by decide +kernel
theorem s176_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 2 = true := by decide +kernel
theorem k176_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k176_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k176_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s176_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k176_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k176_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k176_3_3_26 k h.1 (by omega)
theorem s176_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 4 = true := by decide +kernel
theorem s176_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 5 = true := by decide +kernel
theorem k176_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k176_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k176_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k176_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k176_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k176_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k176_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k176_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k176_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k176_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k176_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s176_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k176_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k176_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k176_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k176_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k176_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k176_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k176_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k176_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k176_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k176_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k176_3_6_130 k h.1 (by omega)
theorem s176_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 3 7 = true := by decide +kernel
theorem s176_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 0 = true := by decide +kernel
theorem s176_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 1 = true := by decide +kernel
theorem s176_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 2 = true := by decide +kernel
theorem s176_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 3 = true := by decide +kernel
theorem s176_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 4 = true := by decide +kernel
theorem s176_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 5 = true := by decide +kernel
theorem k176_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k176_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k176_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k176_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k176_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k176_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k176_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s176_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k176_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k176_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k176_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k176_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k176_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k176_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k176_4_6_126 k h.1 (by omega)
theorem s176_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 4 7 = true := by decide +kernel
theorem s176_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 0 = true := by decide +kernel
theorem s176_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 1 = true := by decide +kernel
theorem s176_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 2 = true := by decide +kernel
theorem s176_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 3 = true := by decide +kernel
theorem s176_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 4 = true := by decide +kernel
theorem s176_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 5 = true := by decide +kernel
theorem k176_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k176_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k176_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k176_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k176_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k176_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k176_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s176_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k176_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k176_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k176_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k176_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k176_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k176_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 176) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (176 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k176_5_6_126 k h.1 (by omega)
theorem s176_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 5 7 = true := by decide +kernel
theorem s176_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 0 = true := by decide +kernel
theorem s176_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 1 = true := by decide +kernel
theorem s176_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 2 = true := by decide +kernel
theorem s176_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 3 = true := by decide +kernel
theorem s176_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 4 = true := by decide +kernel
theorem s176_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 5 = true := by decide +kernel
theorem s176_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 6 = true := by decide +kernel
theorem k176_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k176_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k176_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k176_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k176_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s176_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k176_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k176_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k176_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k176_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 176) ((InDA1.TCasaD 6 6 7).getD (176 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k176_6_7_12 k h.1 (by omega)
theorem col176_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 7 v) = true := by decide +kernel
theorem col176 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 176) 176 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col176_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col176_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col176_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s176_3_0
    · exact s176_3_1
    · exact s176_3_2
    · exact s176_3_3
    · exact s176_3_4
    · exact s176_3_5
    · exact s176_3_6
    · exact s176_3_7
  · fin_cases v
    · exact s176_4_0
    · exact s176_4_1
    · exact s176_4_2
    · exact s176_4_3
    · exact s176_4_4
    · exact s176_4_5
    · exact s176_4_6
    · exact s176_4_7
  · fin_cases v
    · exact s176_5_0
    · exact s176_5_1
    · exact s176_5_2
    · exact s176_5_3
    · exact s176_5_4
    · exact s176_5_5
    · exact s176_5_6
    · exact s176_5_7
  · fin_cases v
    · exact s176_6_0
    · exact s176_6_1
    · exact s176_6_2
    · exact s176_6_3
    · exact s176_6_4
    · exact s176_6_5
    · exact s176_6_6
    · exact s176_6_7
  · exact List.all_eq_true.mp col176_7 v (List.mem_finRange v)
theorem col177_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 0 v) = true := by decide +kernel
theorem col177_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 1 v) = true := by decide +kernel
theorem col177_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 2 v) = true := by decide +kernel
theorem s177_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 0 = true := by decide +kernel
theorem s177_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 1 = true := by decide +kernel
theorem s177_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 2 = true := by decide +kernel
theorem k177_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k177_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k177_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s177_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k177_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k177_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k177_3_3_26 k h.1 (by omega)
theorem s177_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 4 = true := by decide +kernel
theorem s177_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 5 = true := by decide +kernel
theorem k177_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k177_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k177_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k177_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k177_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k177_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k177_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k177_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k177_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k177_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k177_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s177_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k177_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k177_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k177_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k177_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k177_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k177_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k177_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k177_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k177_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k177_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k177_3_6_130 k h.1 (by omega)
theorem s177_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 3 7 = true := by decide +kernel
theorem s177_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 0 = true := by decide +kernel
theorem s177_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 1 = true := by decide +kernel
theorem s177_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 2 = true := by decide +kernel
theorem s177_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 3 = true := by decide +kernel
theorem s177_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 4 = true := by decide +kernel
theorem s177_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 5 = true := by decide +kernel
theorem k177_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k177_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k177_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k177_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k177_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k177_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k177_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s177_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k177_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k177_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k177_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k177_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k177_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k177_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k177_4_6_126 k h.1 (by omega)
theorem s177_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 4 7 = true := by decide +kernel
theorem s177_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 0 = true := by decide +kernel
theorem s177_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 1 = true := by decide +kernel
theorem s177_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 2 = true := by decide +kernel
theorem s177_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 3 = true := by decide +kernel
theorem s177_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 4 = true := by decide +kernel
theorem s177_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 5 = true := by decide +kernel
theorem k177_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k177_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k177_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k177_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k177_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k177_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k177_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s177_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k177_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k177_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k177_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k177_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k177_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k177_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 177) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (177 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k177_5_6_126 k h.1 (by omega)
theorem s177_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 5 7 = true := by decide +kernel
theorem s177_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 0 = true := by decide +kernel
theorem s177_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 1 = true := by decide +kernel
theorem s177_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 2 = true := by decide +kernel
theorem s177_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 3 = true := by decide +kernel
theorem s177_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 4 = true := by decide +kernel
theorem s177_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 5 = true := by decide +kernel
theorem s177_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 6 = true := by decide +kernel
theorem k177_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k177_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k177_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k177_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k177_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s177_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k177_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k177_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k177_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k177_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 177) ((InDA1.TCasaD 6 6 7).getD (177 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k177_6_7_12 k h.1 (by omega)
theorem col177_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 7 v) = true := by decide +kernel
theorem col177 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 177) 177 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col177_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col177_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col177_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s177_3_0
    · exact s177_3_1
    · exact s177_3_2
    · exact s177_3_3
    · exact s177_3_4
    · exact s177_3_5
    · exact s177_3_6
    · exact s177_3_7
  · fin_cases v
    · exact s177_4_0
    · exact s177_4_1
    · exact s177_4_2
    · exact s177_4_3
    · exact s177_4_4
    · exact s177_4_5
    · exact s177_4_6
    · exact s177_4_7
  · fin_cases v
    · exact s177_5_0
    · exact s177_5_1
    · exact s177_5_2
    · exact s177_5_3
    · exact s177_5_4
    · exact s177_5_5
    · exact s177_5_6
    · exact s177_5_7
  · fin_cases v
    · exact s177_6_0
    · exact s177_6_1
    · exact s177_6_2
    · exact s177_6_3
    · exact s177_6_4
    · exact s177_6_5
    · exact s177_6_6
    · exact s177_6_7
  · exact List.all_eq_true.mp col177_7 v (List.mem_finRange v)
theorem col178_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 0 v) = true := by decide +kernel
theorem col178_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 1 v) = true := by decide +kernel
theorem col178_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 2 v) = true := by decide +kernel
theorem s178_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 0 = true := by decide +kernel
theorem s178_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 1 = true := by decide +kernel
theorem s178_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 2 = true := by decide +kernel
theorem k178_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k178_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k178_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s178_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k178_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k178_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k178_3_3_26 k h.1 (by omega)
theorem s178_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 4 = true := by decide +kernel
theorem s178_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 5 = true := by decide +kernel
theorem k178_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k178_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k178_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k178_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k178_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k178_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k178_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k178_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k178_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k178_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k178_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s178_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k178_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k178_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k178_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k178_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k178_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k178_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k178_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k178_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k178_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k178_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k178_3_6_130 k h.1 (by omega)
theorem s178_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 3 7 = true := by decide +kernel
theorem s178_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 0 = true := by decide +kernel
theorem s178_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 1 = true := by decide +kernel
theorem s178_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 2 = true := by decide +kernel
theorem s178_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 3 = true := by decide +kernel
theorem s178_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 4 = true := by decide +kernel
theorem s178_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 5 = true := by decide +kernel
theorem k178_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k178_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k178_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k178_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k178_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k178_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k178_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s178_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k178_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k178_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k178_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k178_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k178_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k178_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k178_4_6_126 k h.1 (by omega)
theorem s178_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 4 7 = true := by decide +kernel
theorem s178_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 0 = true := by decide +kernel
theorem s178_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 1 = true := by decide +kernel
theorem s178_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 2 = true := by decide +kernel
theorem s178_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 3 = true := by decide +kernel
theorem s178_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 4 = true := by decide +kernel
theorem s178_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 5 = true := by decide +kernel
theorem k178_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k178_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k178_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k178_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k178_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k178_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k178_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s178_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k178_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k178_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k178_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k178_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k178_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k178_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 178) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (178 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k178_5_6_126 k h.1 (by omega)
theorem s178_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 5 7 = true := by decide +kernel
theorem s178_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 0 = true := by decide +kernel
theorem s178_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 1 = true := by decide +kernel
theorem s178_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 2 = true := by decide +kernel
theorem s178_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 3 = true := by decide +kernel
theorem s178_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 4 = true := by decide +kernel
theorem s178_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 5 = true := by decide +kernel
theorem s178_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 6 = true := by decide +kernel
theorem k178_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k178_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k178_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k178_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k178_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s178_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k178_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k178_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k178_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k178_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 178) ((InDA1.TCasaD 6 6 7).getD (178 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k178_6_7_12 k h.1 (by omega)
theorem col178_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 7 v) = true := by decide +kernel
theorem col178 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 178) 178 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col178_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col178_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col178_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s178_3_0
    · exact s178_3_1
    · exact s178_3_2
    · exact s178_3_3
    · exact s178_3_4
    · exact s178_3_5
    · exact s178_3_6
    · exact s178_3_7
  · fin_cases v
    · exact s178_4_0
    · exact s178_4_1
    · exact s178_4_2
    · exact s178_4_3
    · exact s178_4_4
    · exact s178_4_5
    · exact s178_4_6
    · exact s178_4_7
  · fin_cases v
    · exact s178_5_0
    · exact s178_5_1
    · exact s178_5_2
    · exact s178_5_3
    · exact s178_5_4
    · exact s178_5_5
    · exact s178_5_6
    · exact s178_5_7
  · fin_cases v
    · exact s178_6_0
    · exact s178_6_1
    · exact s178_6_2
    · exact s178_6_3
    · exact s178_6_4
    · exact s178_6_5
    · exact s178_6_6
    · exact s178_6_7
  · exact List.all_eq_true.mp col178_7 v (List.mem_finRange v)
theorem col179_0 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 0 v) = true := by decide +kernel
theorem col179_1 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 1 v) = true := by decide +kernel
theorem col179_2 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 2 v) = true := by decide +kernel
theorem s179_3_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 0 = true := by decide +kernel
theorem s179_3_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 1 = true := by decide +kernel
theorem s179_3_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 2 = true := by decide +kernel
theorem k179_3_3_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k179_3_3_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k179_3_3_26 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem s179_3_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 3 = true := by
  rw [segOKA_gRC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 3 = 36 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 36)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 0 13 k179_3_3_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 13 13 k179_3_3_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TCasaD 3 3 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 3) (x2SOff 1 3) (nS 1 3)) 26 10 k179_3_3_26 k h.1 (by omega)
theorem s179_3_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 4 = true := by decide +kernel
theorem s179_3_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 5 = true := by decide +kernel
theorem k179_3_6_0 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (0 + k)) = true := by decide +kernel
theorem k179_3_6_13 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (13 + k)) = true := by decide +kernel
theorem k179_3_6_26 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (26 + k)) = true := by decide +kernel
theorem k179_3_6_39 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (39 + k)) = true := by decide +kernel
theorem k179_3_6_52 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (52 + k)) = true := by decide +kernel
theorem k179_3_6_65 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (65 + k)) = true := by decide +kernel
theorem k179_3_6_78 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (78 + k)) = true := by decide +kernel
theorem k179_3_6_91 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (91 + k)) = true := by decide +kernel
theorem k179_3_6_104 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (104 + k)) = true := by decide +kernel
theorem k179_3_6_117 : (List.range 13).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (117 + k)) = true := by decide +kernel
theorem k179_3_6_130 : (List.range 6).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) (130 + k)) = true := by decide +kernel
theorem s179_3_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 13) ∨ (13 ≤ k ∧ k < 26) ∨ (26 ≤ k ∧ k < 39) ∨ (39 ≤ k ∧ k < 52) ∨ (52 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 78) ∨ (78 ≤ k ∧ k < 91) ∨ (91 ≤ k ∧ k < 104) ∨ (104 ≤ k ∧ k < 117) ∨ (117 ≤ k ∧ k < 130) ∨ (130 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 0 13 k179_3_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 13 13 k179_3_6_13 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 26 13 k179_3_6_26 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 39 13 k179_3_6_39 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 52 13 k179_3_6_52 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 65 13 k179_3_6_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 78 13 k179_3_6_78 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 91 13 k179_3_6_91 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 104 13 k179_3_6_104 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 117 13 k179_3_6_117 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 3 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 3) (nS 1 3)) 130 6 k179_3_6_130 k h.1 (by omega)
theorem s179_3_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 3 7 = true := by decide +kernel
theorem s179_4_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 0 = true := by decide +kernel
theorem s179_4_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 1 = true := by decide +kernel
theorem s179_4_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 2 = true := by decide +kernel
theorem s179_4_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 3 = true := by decide +kernel
theorem s179_4_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 4 = true := by decide +kernel
theorem s179_4_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 5 = true := by decide +kernel
theorem k179_4_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (0 + k)) = true := by decide +kernel
theorem k179_4_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (21 + k)) = true := by decide +kernel
theorem k179_4_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (42 + k)) = true := by decide +kernel
theorem k179_4_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (63 + k)) = true := by decide +kernel
theorem k179_4_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (84 + k)) = true := by decide +kernel
theorem k179_4_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (105 + k)) = true := by decide +kernel
theorem k179_4_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) (126 + k)) = true := by decide +kernel
theorem s179_4_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 0 21 k179_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 21 21 k179_4_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 42 21 k179_4_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 63 21 k179_4_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 84 21 k179_4_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 105 21 k179_4_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 4 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 4) (nS 1 4)) 126 10 k179_4_6_126 k h.1 (by omega)
theorem s179_4_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 4 7 = true := by decide +kernel
theorem s179_5_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 0 = true := by decide +kernel
theorem s179_5_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 1 = true := by decide +kernel
theorem s179_5_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 2 = true := by decide +kernel
theorem s179_5_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 3 = true := by decide +kernel
theorem s179_5_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 4 = true := by decide +kernel
theorem s179_5_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 5 = true := by decide +kernel
theorem k179_5_6_0 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (0 + k)) = true := by decide +kernel
theorem k179_5_6_21 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (21 + k)) = true := by decide +kernel
theorem k179_5_6_42 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (42 + k)) = true := by decide +kernel
theorem k179_5_6_63 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (63 + k)) = true := by decide +kernel
theorem k179_5_6_84 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (84 + k)) = true := by decide +kernel
theorem k179_5_6_105 : (List.range 21).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (105 + k)) = true := by decide +kernel
theorem k179_5_6_126 : (List.range 10).all (fun k => (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) (126 + k)) = true := by decide +kernel
theorem s179_5_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 6 = true := by
  rw [segOKA_gRT 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 6 = 136 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 21) ∨ (21 ≤ k ∧ k < 42) ∨ (42 ≤ k ∧ k < 63) ∨ (63 ≤ k ∧ k < 84) ∨ (84 ≤ k ∧ k < 105) ∨ (105 ≤ k ∧ k < 126) ∨ (126 ≤ k ∧ k < 136)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 0 21 k179_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 21 21 k179_5_6_21 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 42 21 k179_5_6_42 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 63 21 k179_5_6_63 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 84 21 k179_5_6_84 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 105 21 k179_5_6_105 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA1g.f0 179) (InDA1.TTsaaD 5 6 6) (posA (x2Mult 1 6) (179 - x2AOff 1 6)) (x2AOff 1 6) (x2SOff 1 5) (nS 1 5)) 126 10 k179_5_6_126 k h.1 (by omega)
theorem s179_5_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 5 7 = true := by decide +kernel
theorem s179_6_0 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 0 = true := by decide +kernel
theorem s179_6_1 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 1 = true := by decide +kernel
theorem s179_6_2 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 2 = true := by decide +kernel
theorem s179_6_3 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 3 = true := by decide +kernel
theorem s179_6_4 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 4 = true := by decide +kernel
theorem s179_6_5 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 5 = true := by decide +kernel
theorem s179_6_6 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 6 = true := by decide +kernel
theorem k179_6_7_0 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (0 + k)) = true := by decide +kernel
theorem k179_6_7_3 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (3 + k)) = true := by decide +kernel
theorem k179_6_7_6 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (6 + k)) = true := by decide +kernel
theorem k179_6_7_9 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (9 + k)) = true := by decide +kernel
theorem k179_6_7_12 : (List.range 3).all (fun k => (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) (12 + k)) = true := by decide +kernel
theorem s179_6_7 : segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 7 = true := by
  rw [segOKA_gPC 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 6 7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 1 7 = 15 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 3) ∨ (3 ≤ k ∧ k < 6) ∨ (6 ≤ k ∧ k < 9) ∨ (9 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 15)) with h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 0 3 k179_6_7_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 3 3 k179_6_7_3 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 6 3 k179_6_7_6 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 9 3 k179_6_7_9 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA1g.f0 179) ((InDA1.TCasaD 6 6 7).getD (179 - x2AOff 1 6) []) (posA (x2Mult 1 7)) (x2AOff 1 7) (x2SOff 1 6) (nS 1 6)) 12 3 k179_6_7_12 k h.1 (by omega)
theorem col179_7 : (List.finRange 8).all (fun v => segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 7 v) = true := by decide +kernel
theorem col179 : ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 179) 179 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col179_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col179_1 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col179_2 v (List.mem_finRange v)
  · fin_cases v
    · exact s179_3_0
    · exact s179_3_1
    · exact s179_3_2
    · exact s179_3_3
    · exact s179_3_4
    · exact s179_3_5
    · exact s179_3_6
    · exact s179_3_7
  · fin_cases v
    · exact s179_4_0
    · exact s179_4_1
    · exact s179_4_2
    · exact s179_4_3
    · exact s179_4_4
    · exact s179_4_5
    · exact s179_4_6
    · exact s179_4_7
  · fin_cases v
    · exact s179_5_0
    · exact s179_5_1
    · exact s179_5_2
    · exact s179_5_3
    · exact s179_5_4
    · exact s179_5_5
    · exact s179_5_6
    · exact s179_5_7
  · fin_cases v
    · exact s179_6_0
    · exact s179_6_1
    · exact s179_6_2
    · exact s179_6_3
    · exact s179_6_4
    · exact s179_6_5
    · exact s179_6_6
    · exact s179_6_7
  · exact List.all_eq_true.mp col179_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA1
