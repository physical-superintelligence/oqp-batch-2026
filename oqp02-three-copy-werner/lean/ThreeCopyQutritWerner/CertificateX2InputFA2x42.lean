module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [210, 215). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col210_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 0 v) = true := by decide +kernel
theorem col210_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 1 v) = true := by decide +kernel
theorem s210_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 0 = true := by decide +kernel
theorem s210_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 1 = true := by decide +kernel
theorem s210_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 2 = true := by decide +kernel
theorem s210_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 3 = true := by decide +kernel
theorem k210_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k210_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k210_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s210_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k210_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k210_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k210_2_4_80 k h.1 (by omega)
theorem s210_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 5 = true := by decide +kernel
theorem s210_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 6 = true := by decide +kernel
theorem s210_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 2 7 = true := by decide +kernel
theorem s210_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 0 = true := by decide +kernel
theorem s210_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 1 = true := by decide +kernel
theorem s210_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 2 = true := by decide +kernel
theorem s210_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 3 = true := by decide +kernel
theorem k210_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k210_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k210_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s210_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k210_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k210_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k210_3_4_80 k h.1 (by omega)
theorem s210_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 5 = true := by decide +kernel
theorem s210_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 6 = true := by decide +kernel
theorem s210_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 3 7 = true := by decide +kernel
theorem s210_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 0 = true := by decide +kernel
theorem s210_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 1 = true := by decide +kernel
theorem s210_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 2 = true := by decide +kernel
theorem s210_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 3 = true := by decide +kernel
theorem k210_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k210_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k210_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k210_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k210_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k210_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k210_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k210_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k210_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k210_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k210_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k210_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k210_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k210_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k210_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k210_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k210_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k210_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k210_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k210_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k210_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s210_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k210_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k210_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k210_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k210_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k210_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k210_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k210_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k210_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k210_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k210_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k210_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k210_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k210_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k210_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k210_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k210_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k210_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k210_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k210_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k210_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k210_4_4_100 k h.1 (by omega)
theorem k210_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k210_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k210_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k210_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k210_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k210_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k210_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k210_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k210_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s210_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k210_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k210_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k210_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k210_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k210_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k210_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k210_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k210_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k210_4_5_40 k h.1 (by omega)
theorem k210_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k210_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k210_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k210_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k210_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k210_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k210_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k210_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k210_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k210_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k210_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s210_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k210_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k210_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k210_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k210_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k210_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k210_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k210_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k210_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k210_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k210_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k210_4_6_50 k h.1 (by omega)
theorem s210_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 4 7 = true := by decide +kernel
theorem s210_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 0 = true := by decide +kernel
theorem s210_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 1 = true := by decide +kernel
theorem s210_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 2 = true := by decide +kernel
theorem s210_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 3 = true := by decide +kernel
theorem k210_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k210_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k210_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k210_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k210_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k210_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k210_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k210_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k210_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k210_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k210_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s210_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k210_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k210_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k210_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k210_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k210_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k210_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k210_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k210_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k210_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k210_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k210_5_4_100 k h.1 (by omega)
theorem k210_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k210_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k210_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k210_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k210_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s210_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k210_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k210_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k210_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k210_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k210_5_5_40 k h.1 (by omega)
theorem k210_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k210_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k210_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k210_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k210_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k210_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s210_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k210_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k210_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k210_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k210_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k210_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 210) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (210 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k210_5_6_50 k h.1 (by omega)
theorem s210_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 5 7 = true := by decide +kernel
theorem col210_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 6 v) = true := by decide +kernel
theorem col210_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 7 v) = true := by decide +kernel
theorem col210 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 210) 210 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col210_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col210_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s210_2_0
    · exact s210_2_1
    · exact s210_2_2
    · exact s210_2_3
    · exact s210_2_4
    · exact s210_2_5
    · exact s210_2_6
    · exact s210_2_7
  · fin_cases v
    · exact s210_3_0
    · exact s210_3_1
    · exact s210_3_2
    · exact s210_3_3
    · exact s210_3_4
    · exact s210_3_5
    · exact s210_3_6
    · exact s210_3_7
  · fin_cases v
    · exact s210_4_0
    · exact s210_4_1
    · exact s210_4_2
    · exact s210_4_3
    · exact s210_4_4
    · exact s210_4_5
    · exact s210_4_6
    · exact s210_4_7
  · fin_cases v
    · exact s210_5_0
    · exact s210_5_1
    · exact s210_5_2
    · exact s210_5_3
    · exact s210_5_4
    · exact s210_5_5
    · exact s210_5_6
    · exact s210_5_7
  · exact List.all_eq_true.mp col210_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col210_7 v (List.mem_finRange v)
theorem col211_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 0 v) = true := by decide +kernel
theorem col211_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 1 v) = true := by decide +kernel
theorem s211_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 0 = true := by decide +kernel
theorem s211_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 1 = true := by decide +kernel
theorem s211_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 2 = true := by decide +kernel
theorem s211_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 3 = true := by decide +kernel
theorem k211_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k211_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k211_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s211_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k211_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k211_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k211_2_4_80 k h.1 (by omega)
theorem s211_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 5 = true := by decide +kernel
theorem s211_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 6 = true := by decide +kernel
theorem s211_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 2 7 = true := by decide +kernel
theorem s211_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 0 = true := by decide +kernel
theorem s211_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 1 = true := by decide +kernel
theorem s211_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 2 = true := by decide +kernel
theorem s211_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 3 = true := by decide +kernel
theorem k211_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k211_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k211_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s211_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k211_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k211_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k211_3_4_80 k h.1 (by omega)
theorem s211_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 5 = true := by decide +kernel
theorem s211_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 6 = true := by decide +kernel
theorem s211_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 3 7 = true := by decide +kernel
theorem s211_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 0 = true := by decide +kernel
theorem s211_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 1 = true := by decide +kernel
theorem s211_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 2 = true := by decide +kernel
theorem s211_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 3 = true := by decide +kernel
theorem k211_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k211_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k211_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k211_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k211_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k211_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k211_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k211_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k211_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k211_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k211_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k211_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k211_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k211_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k211_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k211_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k211_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k211_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k211_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k211_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k211_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s211_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k211_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k211_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k211_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k211_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k211_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k211_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k211_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k211_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k211_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k211_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k211_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k211_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k211_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k211_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k211_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k211_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k211_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k211_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k211_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k211_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k211_4_4_100 k h.1 (by omega)
theorem k211_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k211_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k211_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k211_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k211_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k211_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k211_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k211_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k211_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s211_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k211_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k211_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k211_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k211_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k211_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k211_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k211_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k211_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k211_4_5_40 k h.1 (by omega)
theorem k211_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k211_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k211_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k211_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k211_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k211_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k211_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k211_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k211_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k211_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k211_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s211_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k211_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k211_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k211_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k211_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k211_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k211_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k211_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k211_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k211_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k211_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k211_4_6_50 k h.1 (by omega)
theorem s211_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 4 7 = true := by decide +kernel
theorem s211_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 0 = true := by decide +kernel
theorem s211_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 1 = true := by decide +kernel
theorem s211_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 2 = true := by decide +kernel
theorem s211_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 3 = true := by decide +kernel
theorem k211_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k211_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k211_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k211_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k211_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k211_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k211_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k211_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k211_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k211_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k211_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s211_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k211_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k211_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k211_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k211_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k211_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k211_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k211_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k211_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k211_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k211_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k211_5_4_100 k h.1 (by omega)
theorem k211_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k211_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k211_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k211_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k211_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s211_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k211_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k211_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k211_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k211_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k211_5_5_40 k h.1 (by omega)
theorem k211_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k211_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k211_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k211_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k211_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k211_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s211_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k211_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k211_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k211_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k211_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k211_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 211) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (211 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k211_5_6_50 k h.1 (by omega)
theorem s211_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 5 7 = true := by decide +kernel
theorem col211_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 6 v) = true := by decide +kernel
theorem col211_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 7 v) = true := by decide +kernel
theorem col211 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 211) 211 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col211_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col211_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s211_2_0
    · exact s211_2_1
    · exact s211_2_2
    · exact s211_2_3
    · exact s211_2_4
    · exact s211_2_5
    · exact s211_2_6
    · exact s211_2_7
  · fin_cases v
    · exact s211_3_0
    · exact s211_3_1
    · exact s211_3_2
    · exact s211_3_3
    · exact s211_3_4
    · exact s211_3_5
    · exact s211_3_6
    · exact s211_3_7
  · fin_cases v
    · exact s211_4_0
    · exact s211_4_1
    · exact s211_4_2
    · exact s211_4_3
    · exact s211_4_4
    · exact s211_4_5
    · exact s211_4_6
    · exact s211_4_7
  · fin_cases v
    · exact s211_5_0
    · exact s211_5_1
    · exact s211_5_2
    · exact s211_5_3
    · exact s211_5_4
    · exact s211_5_5
    · exact s211_5_6
    · exact s211_5_7
  · exact List.all_eq_true.mp col211_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col211_7 v (List.mem_finRange v)
theorem col212_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 0 v) = true := by decide +kernel
theorem col212_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 1 v) = true := by decide +kernel
theorem s212_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 0 = true := by decide +kernel
theorem s212_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 1 = true := by decide +kernel
theorem s212_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 2 = true := by decide +kernel
theorem s212_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 3 = true := by decide +kernel
theorem k212_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k212_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k212_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s212_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k212_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k212_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k212_2_4_80 k h.1 (by omega)
theorem s212_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 5 = true := by decide +kernel
theorem s212_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 6 = true := by decide +kernel
theorem s212_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 2 7 = true := by decide +kernel
theorem s212_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 0 = true := by decide +kernel
theorem s212_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 1 = true := by decide +kernel
theorem s212_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 2 = true := by decide +kernel
theorem s212_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 3 = true := by decide +kernel
theorem k212_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k212_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k212_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s212_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k212_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k212_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k212_3_4_80 k h.1 (by omega)
theorem s212_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 5 = true := by decide +kernel
theorem s212_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 6 = true := by decide +kernel
theorem s212_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 3 7 = true := by decide +kernel
theorem s212_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 0 = true := by decide +kernel
theorem s212_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 1 = true := by decide +kernel
theorem s212_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 2 = true := by decide +kernel
theorem s212_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 3 = true := by decide +kernel
theorem k212_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k212_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k212_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k212_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k212_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k212_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k212_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k212_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k212_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k212_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k212_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k212_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k212_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k212_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k212_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k212_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k212_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k212_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k212_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k212_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k212_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s212_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k212_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k212_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k212_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k212_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k212_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k212_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k212_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k212_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k212_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k212_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k212_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k212_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k212_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k212_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k212_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k212_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k212_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k212_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k212_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k212_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k212_4_4_100 k h.1 (by omega)
theorem k212_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k212_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k212_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k212_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k212_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k212_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k212_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k212_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k212_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s212_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k212_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k212_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k212_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k212_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k212_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k212_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k212_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k212_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k212_4_5_40 k h.1 (by omega)
theorem k212_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k212_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k212_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k212_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k212_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k212_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k212_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k212_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k212_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k212_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k212_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s212_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k212_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k212_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k212_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k212_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k212_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k212_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k212_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k212_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k212_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k212_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k212_4_6_50 k h.1 (by omega)
theorem s212_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 4 7 = true := by decide +kernel
theorem s212_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 0 = true := by decide +kernel
theorem s212_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 1 = true := by decide +kernel
theorem s212_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 2 = true := by decide +kernel
theorem s212_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 3 = true := by decide +kernel
theorem k212_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k212_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k212_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k212_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k212_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k212_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k212_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k212_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k212_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k212_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k212_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s212_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k212_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k212_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k212_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k212_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k212_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k212_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k212_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k212_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k212_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k212_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k212_5_4_100 k h.1 (by omega)
theorem k212_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k212_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k212_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k212_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k212_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s212_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k212_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k212_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k212_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k212_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k212_5_5_40 k h.1 (by omega)
theorem k212_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k212_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k212_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k212_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k212_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k212_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s212_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k212_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k212_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k212_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k212_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k212_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 212) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (212 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k212_5_6_50 k h.1 (by omega)
theorem s212_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 5 7 = true := by decide +kernel
theorem col212_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 6 v) = true := by decide +kernel
theorem col212_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 7 v) = true := by decide +kernel
theorem col212 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 212) 212 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col212_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col212_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s212_2_0
    · exact s212_2_1
    · exact s212_2_2
    · exact s212_2_3
    · exact s212_2_4
    · exact s212_2_5
    · exact s212_2_6
    · exact s212_2_7
  · fin_cases v
    · exact s212_3_0
    · exact s212_3_1
    · exact s212_3_2
    · exact s212_3_3
    · exact s212_3_4
    · exact s212_3_5
    · exact s212_3_6
    · exact s212_3_7
  · fin_cases v
    · exact s212_4_0
    · exact s212_4_1
    · exact s212_4_2
    · exact s212_4_3
    · exact s212_4_4
    · exact s212_4_5
    · exact s212_4_6
    · exact s212_4_7
  · fin_cases v
    · exact s212_5_0
    · exact s212_5_1
    · exact s212_5_2
    · exact s212_5_3
    · exact s212_5_4
    · exact s212_5_5
    · exact s212_5_6
    · exact s212_5_7
  · exact List.all_eq_true.mp col212_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col212_7 v (List.mem_finRange v)
theorem col213_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 0 v) = true := by decide +kernel
theorem col213_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 1 v) = true := by decide +kernel
theorem s213_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 0 = true := by decide +kernel
theorem s213_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 1 = true := by decide +kernel
theorem s213_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 2 = true := by decide +kernel
theorem s213_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 3 = true := by decide +kernel
theorem k213_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k213_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k213_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s213_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k213_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k213_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k213_2_4_80 k h.1 (by omega)
theorem s213_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 5 = true := by decide +kernel
theorem s213_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 6 = true := by decide +kernel
theorem s213_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 2 7 = true := by decide +kernel
theorem s213_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 0 = true := by decide +kernel
theorem s213_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 1 = true := by decide +kernel
theorem s213_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 2 = true := by decide +kernel
theorem s213_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 3 = true := by decide +kernel
theorem k213_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k213_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k213_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s213_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k213_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k213_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k213_3_4_80 k h.1 (by omega)
theorem s213_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 5 = true := by decide +kernel
theorem s213_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 6 = true := by decide +kernel
theorem s213_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 3 7 = true := by decide +kernel
theorem s213_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 0 = true := by decide +kernel
theorem s213_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 1 = true := by decide +kernel
theorem s213_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 2 = true := by decide +kernel
theorem s213_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 3 = true := by decide +kernel
theorem k213_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k213_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k213_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k213_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k213_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k213_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k213_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k213_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k213_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k213_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k213_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k213_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k213_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k213_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k213_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k213_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k213_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k213_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k213_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k213_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k213_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s213_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k213_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k213_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k213_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k213_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k213_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k213_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k213_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k213_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k213_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k213_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k213_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k213_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k213_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k213_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k213_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k213_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k213_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k213_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k213_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k213_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k213_4_4_100 k h.1 (by omega)
theorem k213_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k213_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k213_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k213_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k213_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k213_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k213_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k213_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k213_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s213_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k213_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k213_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k213_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k213_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k213_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k213_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k213_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k213_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k213_4_5_40 k h.1 (by omega)
theorem k213_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k213_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k213_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k213_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k213_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k213_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k213_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k213_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k213_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k213_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k213_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s213_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k213_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k213_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k213_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k213_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k213_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k213_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k213_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k213_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k213_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k213_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k213_4_6_50 k h.1 (by omega)
theorem s213_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 4 7 = true := by decide +kernel
theorem s213_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 0 = true := by decide +kernel
theorem s213_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 1 = true := by decide +kernel
theorem s213_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 2 = true := by decide +kernel
theorem s213_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 3 = true := by decide +kernel
theorem k213_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k213_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k213_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k213_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k213_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k213_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k213_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k213_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k213_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k213_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k213_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s213_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k213_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k213_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k213_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k213_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k213_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k213_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k213_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k213_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k213_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k213_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k213_5_4_100 k h.1 (by omega)
theorem k213_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k213_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k213_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k213_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k213_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s213_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k213_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k213_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k213_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k213_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k213_5_5_40 k h.1 (by omega)
theorem k213_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k213_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k213_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k213_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k213_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k213_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s213_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k213_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k213_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k213_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k213_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k213_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 213) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (213 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k213_5_6_50 k h.1 (by omega)
theorem s213_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 5 7 = true := by decide +kernel
theorem col213_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 6 v) = true := by decide +kernel
theorem col213_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 7 v) = true := by decide +kernel
theorem col213 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 213) 213 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col213_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col213_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s213_2_0
    · exact s213_2_1
    · exact s213_2_2
    · exact s213_2_3
    · exact s213_2_4
    · exact s213_2_5
    · exact s213_2_6
    · exact s213_2_7
  · fin_cases v
    · exact s213_3_0
    · exact s213_3_1
    · exact s213_3_2
    · exact s213_3_3
    · exact s213_3_4
    · exact s213_3_5
    · exact s213_3_6
    · exact s213_3_7
  · fin_cases v
    · exact s213_4_0
    · exact s213_4_1
    · exact s213_4_2
    · exact s213_4_3
    · exact s213_4_4
    · exact s213_4_5
    · exact s213_4_6
    · exact s213_4_7
  · fin_cases v
    · exact s213_5_0
    · exact s213_5_1
    · exact s213_5_2
    · exact s213_5_3
    · exact s213_5_4
    · exact s213_5_5
    · exact s213_5_6
    · exact s213_5_7
  · exact List.all_eq_true.mp col213_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col213_7 v (List.mem_finRange v)
theorem col214_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 0 v) = true := by decide +kernel
theorem col214_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 1 v) = true := by decide +kernel
theorem s214_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 0 = true := by decide +kernel
theorem s214_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 1 = true := by decide +kernel
theorem s214_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 2 = true := by decide +kernel
theorem s214_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 3 = true := by decide +kernel
theorem k214_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k214_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k214_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s214_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k214_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k214_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k214_2_4_80 k h.1 (by omega)
theorem s214_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 5 = true := by decide +kernel
theorem s214_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 6 = true := by decide +kernel
theorem s214_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 2 7 = true := by decide +kernel
theorem s214_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 0 = true := by decide +kernel
theorem s214_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 1 = true := by decide +kernel
theorem s214_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 2 = true := by decide +kernel
theorem s214_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 3 = true := by decide +kernel
theorem k214_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k214_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k214_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s214_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k214_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k214_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k214_3_4_80 k h.1 (by omega)
theorem s214_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 5 = true := by decide +kernel
theorem s214_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 6 = true := by decide +kernel
theorem s214_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 3 7 = true := by decide +kernel
theorem s214_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 0 = true := by decide +kernel
theorem s214_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 1 = true := by decide +kernel
theorem s214_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 2 = true := by decide +kernel
theorem s214_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 3 = true := by decide +kernel
theorem k214_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k214_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k214_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k214_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k214_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k214_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k214_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k214_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k214_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k214_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k214_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k214_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k214_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k214_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k214_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k214_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k214_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k214_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k214_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k214_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k214_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s214_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k214_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k214_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k214_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k214_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k214_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k214_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k214_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k214_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k214_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k214_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k214_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k214_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k214_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k214_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k214_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k214_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k214_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k214_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k214_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k214_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k214_4_4_100 k h.1 (by omega)
theorem k214_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k214_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k214_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k214_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k214_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k214_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k214_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k214_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k214_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s214_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k214_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k214_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k214_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k214_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k214_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k214_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k214_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k214_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k214_4_5_40 k h.1 (by omega)
theorem k214_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k214_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k214_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k214_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k214_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k214_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k214_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k214_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k214_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k214_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k214_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s214_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k214_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k214_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k214_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k214_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k214_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k214_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k214_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k214_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k214_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k214_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k214_4_6_50 k h.1 (by omega)
theorem s214_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 4 7 = true := by decide +kernel
theorem s214_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 0 = true := by decide +kernel
theorem s214_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 1 = true := by decide +kernel
theorem s214_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 2 = true := by decide +kernel
theorem s214_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 3 = true := by decide +kernel
theorem k214_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k214_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k214_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k214_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k214_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k214_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k214_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k214_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k214_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k214_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k214_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s214_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k214_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k214_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k214_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k214_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k214_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k214_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k214_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k214_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k214_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k214_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k214_5_4_100 k h.1 (by omega)
theorem k214_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k214_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k214_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k214_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k214_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s214_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k214_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k214_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k214_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k214_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k214_5_5_40 k h.1 (by omega)
theorem k214_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k214_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k214_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k214_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k214_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k214_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s214_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k214_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k214_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k214_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k214_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k214_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 214) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (214 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k214_5_6_50 k h.1 (by omega)
theorem s214_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 5 7 = true := by decide +kernel
theorem col214_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 6 v) = true := by decide +kernel
theorem col214_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 7 v) = true := by decide +kernel
theorem col214 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 214) 214 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col214_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col214_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s214_2_0
    · exact s214_2_1
    · exact s214_2_2
    · exact s214_2_3
    · exact s214_2_4
    · exact s214_2_5
    · exact s214_2_6
    · exact s214_2_7
  · fin_cases v
    · exact s214_3_0
    · exact s214_3_1
    · exact s214_3_2
    · exact s214_3_3
    · exact s214_3_4
    · exact s214_3_5
    · exact s214_3_6
    · exact s214_3_7
  · fin_cases v
    · exact s214_4_0
    · exact s214_4_1
    · exact s214_4_2
    · exact s214_4_3
    · exact s214_4_4
    · exact s214_4_5
    · exact s214_4_6
    · exact s214_4_7
  · fin_cases v
    · exact s214_5_0
    · exact s214_5_1
    · exact s214_5_2
    · exact s214_5_3
    · exact s214_5_4
    · exact s214_5_5
    · exact s214_5_6
    · exact s214_5_7
  · exact List.all_eq_true.mp col214_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col214_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
