module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [140, 145). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col140_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 0 v) = true := by decide +kernel
theorem col140_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 1 v) = true := by decide +kernel
theorem s140_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 0 = true := by decide +kernel
theorem s140_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 1 = true := by decide +kernel
theorem s140_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 2 = true := by decide +kernel
theorem s140_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 3 = true := by decide +kernel
theorem k140_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k140_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k140_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s140_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k140_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k140_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k140_2_4_80 k h.1 (by omega)
theorem s140_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 5 = true := by decide +kernel
theorem s140_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 6 = true := by decide +kernel
theorem s140_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 2 7 = true := by decide +kernel
theorem s140_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 0 = true := by decide +kernel
theorem s140_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 1 = true := by decide +kernel
theorem s140_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 2 = true := by decide +kernel
theorem s140_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 3 = true := by decide +kernel
theorem k140_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k140_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k140_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s140_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k140_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k140_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k140_3_4_80 k h.1 (by omega)
theorem s140_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 5 = true := by decide +kernel
theorem s140_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 6 = true := by decide +kernel
theorem s140_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 3 7 = true := by decide +kernel
theorem s140_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 0 = true := by decide +kernel
theorem s140_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 1 = true := by decide +kernel
theorem s140_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 2 = true := by decide +kernel
theorem s140_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 3 = true := by decide +kernel
theorem k140_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k140_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k140_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k140_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k140_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k140_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k140_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k140_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k140_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k140_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k140_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k140_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k140_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k140_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k140_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k140_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k140_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k140_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k140_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k140_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k140_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s140_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k140_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k140_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k140_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k140_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k140_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k140_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k140_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k140_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k140_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k140_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k140_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k140_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k140_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k140_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k140_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k140_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k140_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k140_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k140_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k140_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k140_4_4_100 k h.1 (by omega)
theorem k140_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k140_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k140_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k140_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k140_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k140_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k140_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k140_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k140_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s140_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k140_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k140_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k140_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k140_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k140_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k140_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k140_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k140_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 140) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (140 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k140_4_5_40 k h.1 (by omega)
theorem k140_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k140_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k140_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k140_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k140_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k140_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k140_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k140_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k140_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k140_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k140_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s140_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k140_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k140_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k140_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k140_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k140_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k140_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k140_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k140_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k140_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k140_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TTsaaD 4 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k140_4_6_50 k h.1 (by omega)
theorem s140_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 4 7 = true := by decide +kernel
theorem s140_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 0 = true := by decide +kernel
theorem s140_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 1 = true := by decide +kernel
theorem s140_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 2 = true := by decide +kernel
theorem s140_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 3 = true := by decide +kernel
theorem s140_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 4 = true := by decide +kernel
theorem s140_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 5 = true := by decide +kernel
theorem k140_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k140_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k140_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k140_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k140_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k140_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s140_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k140_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k140_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k140_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k140_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k140_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 140) ((InDA2.TCasaD 5 5 6).getD (140 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k140_5_6_50 k h.1 (by omega)
theorem s140_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 5 7 = true := by decide +kernel
theorem col140_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 6 v) = true := by decide +kernel
theorem col140_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 7 v) = true := by decide +kernel
theorem col140 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 140) 140 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col140_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col140_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s140_2_0
    · exact s140_2_1
    · exact s140_2_2
    · exact s140_2_3
    · exact s140_2_4
    · exact s140_2_5
    · exact s140_2_6
    · exact s140_2_7
  · fin_cases v
    · exact s140_3_0
    · exact s140_3_1
    · exact s140_3_2
    · exact s140_3_3
    · exact s140_3_4
    · exact s140_3_5
    · exact s140_3_6
    · exact s140_3_7
  · fin_cases v
    · exact s140_4_0
    · exact s140_4_1
    · exact s140_4_2
    · exact s140_4_3
    · exact s140_4_4
    · exact s140_4_5
    · exact s140_4_6
    · exact s140_4_7
  · fin_cases v
    · exact s140_5_0
    · exact s140_5_1
    · exact s140_5_2
    · exact s140_5_3
    · exact s140_5_4
    · exact s140_5_5
    · exact s140_5_6
    · exact s140_5_7
  · exact List.all_eq_true.mp col140_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col140_7 v (List.mem_finRange v)
theorem col141_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 0 v) = true := by decide +kernel
theorem col141_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 1 v) = true := by decide +kernel
theorem s141_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 0 = true := by decide +kernel
theorem s141_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 1 = true := by decide +kernel
theorem s141_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 2 = true := by decide +kernel
theorem s141_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 3 = true := by decide +kernel
theorem k141_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k141_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k141_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s141_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k141_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k141_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k141_2_4_80 k h.1 (by omega)
theorem s141_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 5 = true := by decide +kernel
theorem s141_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 6 = true := by decide +kernel
theorem s141_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 2 7 = true := by decide +kernel
theorem s141_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 0 = true := by decide +kernel
theorem s141_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 1 = true := by decide +kernel
theorem s141_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 2 = true := by decide +kernel
theorem s141_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 3 = true := by decide +kernel
theorem k141_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k141_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k141_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s141_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k141_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k141_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k141_3_4_80 k h.1 (by omega)
theorem s141_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 5 = true := by decide +kernel
theorem s141_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 6 = true := by decide +kernel
theorem s141_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 3 7 = true := by decide +kernel
theorem s141_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 0 = true := by decide +kernel
theorem s141_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 1 = true := by decide +kernel
theorem s141_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 2 = true := by decide +kernel
theorem s141_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 3 = true := by decide +kernel
theorem k141_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k141_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k141_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k141_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k141_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k141_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k141_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k141_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k141_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k141_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k141_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k141_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k141_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k141_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k141_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k141_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k141_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k141_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k141_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k141_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k141_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s141_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k141_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k141_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k141_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k141_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k141_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k141_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k141_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k141_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k141_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k141_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k141_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k141_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k141_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k141_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k141_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k141_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k141_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k141_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k141_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k141_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k141_4_4_100 k h.1 (by omega)
theorem k141_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k141_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k141_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k141_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k141_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k141_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k141_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k141_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k141_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s141_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k141_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k141_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k141_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k141_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k141_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k141_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k141_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k141_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 141) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (141 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k141_4_5_40 k h.1 (by omega)
theorem k141_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k141_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k141_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k141_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k141_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k141_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k141_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k141_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k141_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k141_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k141_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s141_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k141_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k141_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k141_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k141_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k141_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k141_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k141_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k141_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k141_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k141_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TTsaaD 4 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k141_4_6_50 k h.1 (by omega)
theorem s141_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 4 7 = true := by decide +kernel
theorem s141_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 0 = true := by decide +kernel
theorem s141_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 1 = true := by decide +kernel
theorem s141_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 2 = true := by decide +kernel
theorem s141_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 3 = true := by decide +kernel
theorem s141_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 4 = true := by decide +kernel
theorem s141_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 5 = true := by decide +kernel
theorem k141_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k141_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k141_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k141_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k141_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k141_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s141_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k141_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k141_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k141_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k141_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k141_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 141) ((InDA2.TCasaD 5 5 6).getD (141 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k141_5_6_50 k h.1 (by omega)
theorem s141_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 5 7 = true := by decide +kernel
theorem col141_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 6 v) = true := by decide +kernel
theorem col141_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 7 v) = true := by decide +kernel
theorem col141 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 141) 141 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col141_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col141_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s141_2_0
    · exact s141_2_1
    · exact s141_2_2
    · exact s141_2_3
    · exact s141_2_4
    · exact s141_2_5
    · exact s141_2_6
    · exact s141_2_7
  · fin_cases v
    · exact s141_3_0
    · exact s141_3_1
    · exact s141_3_2
    · exact s141_3_3
    · exact s141_3_4
    · exact s141_3_5
    · exact s141_3_6
    · exact s141_3_7
  · fin_cases v
    · exact s141_4_0
    · exact s141_4_1
    · exact s141_4_2
    · exact s141_4_3
    · exact s141_4_4
    · exact s141_4_5
    · exact s141_4_6
    · exact s141_4_7
  · fin_cases v
    · exact s141_5_0
    · exact s141_5_1
    · exact s141_5_2
    · exact s141_5_3
    · exact s141_5_4
    · exact s141_5_5
    · exact s141_5_6
    · exact s141_5_7
  · exact List.all_eq_true.mp col141_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col141_7 v (List.mem_finRange v)
theorem col142_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 0 v) = true := by decide +kernel
theorem col142_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 1 v) = true := by decide +kernel
theorem s142_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 0 = true := by decide +kernel
theorem s142_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 1 = true := by decide +kernel
theorem s142_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 2 = true := by decide +kernel
theorem s142_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 3 = true := by decide +kernel
theorem k142_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k142_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k142_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s142_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k142_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k142_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k142_2_4_80 k h.1 (by omega)
theorem s142_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 5 = true := by decide +kernel
theorem s142_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 6 = true := by decide +kernel
theorem s142_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 2 7 = true := by decide +kernel
theorem s142_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 0 = true := by decide +kernel
theorem s142_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 1 = true := by decide +kernel
theorem s142_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 2 = true := by decide +kernel
theorem s142_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 3 = true := by decide +kernel
theorem k142_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k142_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k142_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s142_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k142_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k142_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k142_3_4_80 k h.1 (by omega)
theorem s142_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 5 = true := by decide +kernel
theorem s142_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 6 = true := by decide +kernel
theorem s142_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 3 7 = true := by decide +kernel
theorem s142_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 0 = true := by decide +kernel
theorem s142_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 1 = true := by decide +kernel
theorem s142_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 2 = true := by decide +kernel
theorem s142_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 3 = true := by decide +kernel
theorem k142_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k142_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k142_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k142_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k142_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k142_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k142_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k142_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k142_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k142_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k142_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k142_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k142_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k142_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k142_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k142_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k142_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k142_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k142_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k142_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k142_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s142_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k142_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k142_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k142_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k142_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k142_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k142_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k142_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k142_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k142_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k142_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k142_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k142_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k142_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k142_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k142_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k142_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k142_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k142_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k142_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k142_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k142_4_4_100 k h.1 (by omega)
theorem k142_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k142_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k142_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k142_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k142_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k142_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k142_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k142_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k142_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s142_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k142_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k142_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k142_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k142_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k142_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k142_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k142_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k142_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 142) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (142 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k142_4_5_40 k h.1 (by omega)
theorem k142_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k142_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k142_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k142_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k142_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k142_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k142_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k142_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k142_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k142_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k142_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s142_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k142_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k142_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k142_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k142_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k142_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k142_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k142_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k142_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k142_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k142_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TTsaaD 4 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k142_4_6_50 k h.1 (by omega)
theorem s142_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 4 7 = true := by decide +kernel
theorem s142_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 0 = true := by decide +kernel
theorem s142_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 1 = true := by decide +kernel
theorem s142_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 2 = true := by decide +kernel
theorem s142_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 3 = true := by decide +kernel
theorem s142_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 4 = true := by decide +kernel
theorem s142_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 5 = true := by decide +kernel
theorem k142_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k142_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k142_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k142_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k142_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k142_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s142_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k142_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k142_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k142_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k142_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k142_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 142) ((InDA2.TCasaD 5 5 6).getD (142 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k142_5_6_50 k h.1 (by omega)
theorem s142_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 5 7 = true := by decide +kernel
theorem col142_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 6 v) = true := by decide +kernel
theorem col142_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 7 v) = true := by decide +kernel
theorem col142 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 142) 142 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col142_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col142_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s142_2_0
    · exact s142_2_1
    · exact s142_2_2
    · exact s142_2_3
    · exact s142_2_4
    · exact s142_2_5
    · exact s142_2_6
    · exact s142_2_7
  · fin_cases v
    · exact s142_3_0
    · exact s142_3_1
    · exact s142_3_2
    · exact s142_3_3
    · exact s142_3_4
    · exact s142_3_5
    · exact s142_3_6
    · exact s142_3_7
  · fin_cases v
    · exact s142_4_0
    · exact s142_4_1
    · exact s142_4_2
    · exact s142_4_3
    · exact s142_4_4
    · exact s142_4_5
    · exact s142_4_6
    · exact s142_4_7
  · fin_cases v
    · exact s142_5_0
    · exact s142_5_1
    · exact s142_5_2
    · exact s142_5_3
    · exact s142_5_4
    · exact s142_5_5
    · exact s142_5_6
    · exact s142_5_7
  · exact List.all_eq_true.mp col142_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col142_7 v (List.mem_finRange v)
theorem col143_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 0 v) = true := by decide +kernel
theorem col143_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 1 v) = true := by decide +kernel
theorem s143_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 0 = true := by decide +kernel
theorem s143_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 1 = true := by decide +kernel
theorem s143_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 2 = true := by decide +kernel
theorem s143_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 3 = true := by decide +kernel
theorem k143_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k143_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k143_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s143_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k143_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k143_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k143_2_4_80 k h.1 (by omega)
theorem s143_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 5 = true := by decide +kernel
theorem s143_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 6 = true := by decide +kernel
theorem s143_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 2 7 = true := by decide +kernel
theorem s143_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 0 = true := by decide +kernel
theorem s143_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 1 = true := by decide +kernel
theorem s143_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 2 = true := by decide +kernel
theorem s143_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 3 = true := by decide +kernel
theorem k143_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k143_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k143_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s143_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k143_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k143_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k143_3_4_80 k h.1 (by omega)
theorem s143_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 5 = true := by decide +kernel
theorem s143_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 6 = true := by decide +kernel
theorem s143_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 3 7 = true := by decide +kernel
theorem s143_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 0 = true := by decide +kernel
theorem s143_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 1 = true := by decide +kernel
theorem s143_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 2 = true := by decide +kernel
theorem s143_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 3 = true := by decide +kernel
theorem k143_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k143_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k143_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k143_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k143_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k143_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k143_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k143_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k143_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k143_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k143_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k143_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k143_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k143_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k143_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k143_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k143_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k143_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k143_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k143_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k143_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s143_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k143_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k143_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k143_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k143_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k143_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k143_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k143_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k143_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k143_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k143_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k143_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k143_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k143_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k143_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k143_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k143_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k143_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k143_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k143_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k143_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k143_4_4_100 k h.1 (by omega)
theorem k143_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k143_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k143_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k143_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k143_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k143_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k143_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k143_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k143_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s143_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k143_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k143_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k143_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k143_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k143_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k143_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k143_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k143_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 143) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (143 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k143_4_5_40 k h.1 (by omega)
theorem k143_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k143_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k143_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k143_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k143_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k143_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k143_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k143_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k143_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k143_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k143_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s143_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k143_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k143_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k143_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k143_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k143_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k143_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k143_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k143_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k143_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k143_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TTsaaD 4 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k143_4_6_50 k h.1 (by omega)
theorem s143_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 4 7 = true := by decide +kernel
theorem s143_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 0 = true := by decide +kernel
theorem s143_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 1 = true := by decide +kernel
theorem s143_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 2 = true := by decide +kernel
theorem s143_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 3 = true := by decide +kernel
theorem s143_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 4 = true := by decide +kernel
theorem s143_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 5 = true := by decide +kernel
theorem k143_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k143_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k143_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k143_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k143_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k143_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s143_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k143_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k143_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k143_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k143_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k143_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 143) ((InDA2.TCasaD 5 5 6).getD (143 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k143_5_6_50 k h.1 (by omega)
theorem s143_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 5 7 = true := by decide +kernel
theorem col143_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 6 v) = true := by decide +kernel
theorem col143_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 7 v) = true := by decide +kernel
theorem col143 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 143) 143 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col143_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col143_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s143_2_0
    · exact s143_2_1
    · exact s143_2_2
    · exact s143_2_3
    · exact s143_2_4
    · exact s143_2_5
    · exact s143_2_6
    · exact s143_2_7
  · fin_cases v
    · exact s143_3_0
    · exact s143_3_1
    · exact s143_3_2
    · exact s143_3_3
    · exact s143_3_4
    · exact s143_3_5
    · exact s143_3_6
    · exact s143_3_7
  · fin_cases v
    · exact s143_4_0
    · exact s143_4_1
    · exact s143_4_2
    · exact s143_4_3
    · exact s143_4_4
    · exact s143_4_5
    · exact s143_4_6
    · exact s143_4_7
  · fin_cases v
    · exact s143_5_0
    · exact s143_5_1
    · exact s143_5_2
    · exact s143_5_3
    · exact s143_5_4
    · exact s143_5_5
    · exact s143_5_6
    · exact s143_5_7
  · exact List.all_eq_true.mp col143_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col143_7 v (List.mem_finRange v)
theorem col144_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 0 v) = true := by decide +kernel
theorem col144_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 1 v) = true := by decide +kernel
theorem s144_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 0 = true := by decide +kernel
theorem s144_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 1 = true := by decide +kernel
theorem s144_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 2 = true := by decide +kernel
theorem s144_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 3 = true := by decide +kernel
theorem k144_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k144_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k144_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s144_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k144_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k144_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k144_2_4_80 k h.1 (by omega)
theorem s144_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 5 = true := by decide +kernel
theorem s144_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 6 = true := by decide +kernel
theorem s144_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 2 7 = true := by decide +kernel
theorem s144_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 0 = true := by decide +kernel
theorem s144_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 1 = true := by decide +kernel
theorem s144_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 2 = true := by decide +kernel
theorem s144_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 3 = true := by decide +kernel
theorem k144_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k144_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k144_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s144_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k144_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k144_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k144_3_4_80 k h.1 (by omega)
theorem s144_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 5 = true := by decide +kernel
theorem s144_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 6 = true := by decide +kernel
theorem s144_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 3 7 = true := by decide +kernel
theorem s144_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 0 = true := by decide +kernel
theorem s144_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 1 = true := by decide +kernel
theorem s144_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 2 = true := by decide +kernel
theorem s144_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 3 = true := by decide +kernel
theorem k144_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k144_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k144_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k144_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k144_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k144_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k144_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k144_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k144_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k144_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k144_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k144_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k144_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k144_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k144_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k144_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k144_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k144_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k144_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k144_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k144_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s144_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k144_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k144_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k144_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k144_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k144_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k144_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k144_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k144_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k144_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k144_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k144_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k144_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k144_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k144_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k144_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k144_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k144_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k144_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k144_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k144_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k144_4_4_100 k h.1 (by omega)
theorem k144_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k144_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k144_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k144_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k144_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k144_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k144_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k144_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k144_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s144_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k144_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k144_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k144_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k144_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k144_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k144_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k144_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k144_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 144) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (144 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k144_4_5_40 k h.1 (by omega)
theorem k144_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k144_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k144_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k144_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k144_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k144_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k144_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k144_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k144_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k144_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k144_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s144_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k144_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k144_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k144_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k144_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k144_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k144_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k144_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k144_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k144_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k144_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TTsaaD 4 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k144_4_6_50 k h.1 (by omega)
theorem s144_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 4 7 = true := by decide +kernel
theorem s144_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 0 = true := by decide +kernel
theorem s144_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 1 = true := by decide +kernel
theorem s144_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 2 = true := by decide +kernel
theorem s144_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 3 = true := by decide +kernel
theorem s144_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 4 = true := by decide +kernel
theorem s144_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 5 = true := by decide +kernel
theorem k144_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k144_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k144_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k144_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k144_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k144_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s144_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k144_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k144_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k144_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k144_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k144_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 144) ((InDA2.TCasaD 5 5 6).getD (144 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k144_5_6_50 k h.1 (by omega)
theorem s144_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 5 7 = true := by decide +kernel
theorem col144_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 6 v) = true := by decide +kernel
theorem col144_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 7 v) = true := by decide +kernel
theorem col144 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 144) 144 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col144_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col144_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s144_2_0
    · exact s144_2_1
    · exact s144_2_2
    · exact s144_2_3
    · exact s144_2_4
    · exact s144_2_5
    · exact s144_2_6
    · exact s144_2_7
  · fin_cases v
    · exact s144_3_0
    · exact s144_3_1
    · exact s144_3_2
    · exact s144_3_3
    · exact s144_3_4
    · exact s144_3_5
    · exact s144_3_6
    · exact s144_3_7
  · fin_cases v
    · exact s144_4_0
    · exact s144_4_1
    · exact s144_4_2
    · exact s144_4_3
    · exact s144_4_4
    · exact s144_4_5
    · exact s144_4_6
    · exact s144_4_7
  · fin_cases v
    · exact s144_5_0
    · exact s144_5_1
    · exact s144_5_2
    · exact s144_5_3
    · exact s144_5_4
    · exact s144_5_5
    · exact s144_5_6
    · exact s144_5_7
  · exact List.all_eq_true.mp col144_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col144_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
