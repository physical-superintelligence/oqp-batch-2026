module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [160, 165). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col160_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 0 v) = true := by decide +kernel
theorem col160_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 1 v) = true := by decide +kernel
theorem s160_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 0 = true := by decide +kernel
theorem s160_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 1 = true := by decide +kernel
theorem s160_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 2 = true := by decide +kernel
theorem s160_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 3 = true := by decide +kernel
theorem k160_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k160_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k160_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s160_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k160_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k160_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k160_2_4_80 k h.1 (by omega)
theorem s160_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 5 = true := by decide +kernel
theorem s160_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 6 = true := by decide +kernel
theorem s160_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 2 7 = true := by decide +kernel
theorem s160_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 0 = true := by decide +kernel
theorem s160_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 1 = true := by decide +kernel
theorem s160_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 2 = true := by decide +kernel
theorem s160_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 3 = true := by decide +kernel
theorem k160_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k160_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k160_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s160_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k160_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k160_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k160_3_4_80 k h.1 (by omega)
theorem s160_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 5 = true := by decide +kernel
theorem s160_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 6 = true := by decide +kernel
theorem s160_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 3 7 = true := by decide +kernel
theorem s160_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 0 = true := by decide +kernel
theorem s160_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 1 = true := by decide +kernel
theorem s160_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 2 = true := by decide +kernel
theorem s160_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 3 = true := by decide +kernel
theorem k160_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k160_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k160_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k160_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k160_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k160_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k160_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k160_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k160_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k160_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k160_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k160_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k160_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k160_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k160_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k160_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k160_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k160_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k160_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k160_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k160_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s160_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k160_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k160_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k160_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k160_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k160_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k160_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k160_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k160_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k160_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k160_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k160_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k160_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k160_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k160_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k160_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k160_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k160_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k160_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k160_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k160_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k160_4_4_100 k h.1 (by omega)
theorem k160_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k160_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k160_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k160_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k160_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k160_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k160_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k160_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k160_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s160_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k160_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k160_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k160_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k160_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k160_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k160_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k160_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k160_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 160) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (160 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k160_4_5_40 k h.1 (by omega)
theorem k160_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k160_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k160_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k160_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k160_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k160_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k160_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k160_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k160_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k160_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k160_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s160_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k160_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k160_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k160_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k160_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k160_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k160_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k160_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k160_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k160_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k160_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TTsaaD 4 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k160_4_6_50 k h.1 (by omega)
theorem s160_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 4 7 = true := by decide +kernel
theorem s160_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 0 = true := by decide +kernel
theorem s160_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 1 = true := by decide +kernel
theorem s160_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 2 = true := by decide +kernel
theorem s160_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 3 = true := by decide +kernel
theorem s160_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 4 = true := by decide +kernel
theorem s160_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 5 = true := by decide +kernel
theorem k160_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k160_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k160_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k160_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k160_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k160_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s160_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k160_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k160_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k160_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k160_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k160_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 160) ((InDA2.TCasaD 5 5 6).getD (160 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k160_5_6_50 k h.1 (by omega)
theorem s160_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 5 7 = true := by decide +kernel
theorem col160_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 6 v) = true := by decide +kernel
theorem col160_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 7 v) = true := by decide +kernel
theorem col160 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 160) 160 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col160_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col160_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s160_2_0
    · exact s160_2_1
    · exact s160_2_2
    · exact s160_2_3
    · exact s160_2_4
    · exact s160_2_5
    · exact s160_2_6
    · exact s160_2_7
  · fin_cases v
    · exact s160_3_0
    · exact s160_3_1
    · exact s160_3_2
    · exact s160_3_3
    · exact s160_3_4
    · exact s160_3_5
    · exact s160_3_6
    · exact s160_3_7
  · fin_cases v
    · exact s160_4_0
    · exact s160_4_1
    · exact s160_4_2
    · exact s160_4_3
    · exact s160_4_4
    · exact s160_4_5
    · exact s160_4_6
    · exact s160_4_7
  · fin_cases v
    · exact s160_5_0
    · exact s160_5_1
    · exact s160_5_2
    · exact s160_5_3
    · exact s160_5_4
    · exact s160_5_5
    · exact s160_5_6
    · exact s160_5_7
  · exact List.all_eq_true.mp col160_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col160_7 v (List.mem_finRange v)
theorem col161_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 0 v) = true := by decide +kernel
theorem col161_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 1 v) = true := by decide +kernel
theorem s161_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 0 = true := by decide +kernel
theorem s161_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 1 = true := by decide +kernel
theorem s161_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 2 = true := by decide +kernel
theorem s161_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 3 = true := by decide +kernel
theorem k161_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k161_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k161_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s161_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k161_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k161_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k161_2_4_80 k h.1 (by omega)
theorem s161_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 5 = true := by decide +kernel
theorem s161_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 6 = true := by decide +kernel
theorem s161_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 2 7 = true := by decide +kernel
theorem s161_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 0 = true := by decide +kernel
theorem s161_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 1 = true := by decide +kernel
theorem s161_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 2 = true := by decide +kernel
theorem s161_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 3 = true := by decide +kernel
theorem k161_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k161_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k161_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s161_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k161_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k161_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k161_3_4_80 k h.1 (by omega)
theorem s161_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 5 = true := by decide +kernel
theorem s161_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 6 = true := by decide +kernel
theorem s161_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 3 7 = true := by decide +kernel
theorem s161_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 0 = true := by decide +kernel
theorem s161_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 1 = true := by decide +kernel
theorem s161_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 2 = true := by decide +kernel
theorem s161_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 3 = true := by decide +kernel
theorem k161_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k161_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k161_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k161_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k161_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k161_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k161_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k161_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k161_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k161_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k161_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k161_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k161_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k161_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k161_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k161_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k161_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k161_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k161_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k161_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k161_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s161_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k161_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k161_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k161_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k161_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k161_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k161_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k161_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k161_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k161_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k161_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k161_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k161_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k161_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k161_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k161_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k161_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k161_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k161_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k161_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k161_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k161_4_4_100 k h.1 (by omega)
theorem k161_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k161_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k161_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k161_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k161_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k161_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k161_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k161_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k161_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s161_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k161_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k161_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k161_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k161_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k161_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k161_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k161_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k161_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 161) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (161 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k161_4_5_40 k h.1 (by omega)
theorem k161_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k161_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k161_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k161_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k161_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k161_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k161_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k161_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k161_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k161_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k161_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s161_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k161_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k161_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k161_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k161_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k161_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k161_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k161_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k161_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k161_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k161_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TTsaaD 4 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k161_4_6_50 k h.1 (by omega)
theorem s161_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 4 7 = true := by decide +kernel
theorem s161_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 0 = true := by decide +kernel
theorem s161_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 1 = true := by decide +kernel
theorem s161_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 2 = true := by decide +kernel
theorem s161_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 3 = true := by decide +kernel
theorem s161_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 4 = true := by decide +kernel
theorem s161_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 5 = true := by decide +kernel
theorem k161_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k161_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k161_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k161_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k161_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k161_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s161_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k161_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k161_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k161_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k161_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k161_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 161) ((InDA2.TCasaD 5 5 6).getD (161 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k161_5_6_50 k h.1 (by omega)
theorem s161_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 5 7 = true := by decide +kernel
theorem col161_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 6 v) = true := by decide +kernel
theorem col161_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 7 v) = true := by decide +kernel
theorem col161 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 161) 161 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col161_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col161_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s161_2_0
    · exact s161_2_1
    · exact s161_2_2
    · exact s161_2_3
    · exact s161_2_4
    · exact s161_2_5
    · exact s161_2_6
    · exact s161_2_7
  · fin_cases v
    · exact s161_3_0
    · exact s161_3_1
    · exact s161_3_2
    · exact s161_3_3
    · exact s161_3_4
    · exact s161_3_5
    · exact s161_3_6
    · exact s161_3_7
  · fin_cases v
    · exact s161_4_0
    · exact s161_4_1
    · exact s161_4_2
    · exact s161_4_3
    · exact s161_4_4
    · exact s161_4_5
    · exact s161_4_6
    · exact s161_4_7
  · fin_cases v
    · exact s161_5_0
    · exact s161_5_1
    · exact s161_5_2
    · exact s161_5_3
    · exact s161_5_4
    · exact s161_5_5
    · exact s161_5_6
    · exact s161_5_7
  · exact List.all_eq_true.mp col161_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col161_7 v (List.mem_finRange v)
theorem col162_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 0 v) = true := by decide +kernel
theorem col162_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 1 v) = true := by decide +kernel
theorem s162_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 0 = true := by decide +kernel
theorem s162_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 1 = true := by decide +kernel
theorem s162_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 2 = true := by decide +kernel
theorem s162_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 3 = true := by decide +kernel
theorem k162_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k162_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k162_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s162_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k162_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k162_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k162_2_4_80 k h.1 (by omega)
theorem s162_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 5 = true := by decide +kernel
theorem s162_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 6 = true := by decide +kernel
theorem s162_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 2 7 = true := by decide +kernel
theorem s162_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 0 = true := by decide +kernel
theorem s162_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 1 = true := by decide +kernel
theorem s162_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 2 = true := by decide +kernel
theorem s162_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 3 = true := by decide +kernel
theorem k162_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k162_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k162_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s162_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k162_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k162_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k162_3_4_80 k h.1 (by omega)
theorem s162_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 5 = true := by decide +kernel
theorem s162_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 6 = true := by decide +kernel
theorem s162_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 3 7 = true := by decide +kernel
theorem s162_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 0 = true := by decide +kernel
theorem s162_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 1 = true := by decide +kernel
theorem s162_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 2 = true := by decide +kernel
theorem s162_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 3 = true := by decide +kernel
theorem k162_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k162_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k162_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k162_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k162_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k162_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k162_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k162_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k162_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k162_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k162_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k162_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k162_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k162_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k162_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k162_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k162_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k162_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k162_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k162_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k162_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s162_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k162_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k162_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k162_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k162_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k162_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k162_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k162_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k162_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k162_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k162_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k162_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k162_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k162_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k162_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k162_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k162_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k162_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k162_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k162_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k162_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k162_4_4_100 k h.1 (by omega)
theorem k162_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k162_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k162_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k162_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k162_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k162_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k162_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k162_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k162_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s162_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k162_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k162_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k162_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k162_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k162_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k162_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k162_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k162_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 162) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (162 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k162_4_5_40 k h.1 (by omega)
theorem k162_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k162_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k162_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k162_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k162_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k162_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k162_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k162_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k162_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k162_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k162_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s162_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k162_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k162_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k162_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k162_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k162_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k162_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k162_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k162_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k162_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k162_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TTsaaD 4 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k162_4_6_50 k h.1 (by omega)
theorem s162_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 4 7 = true := by decide +kernel
theorem s162_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 0 = true := by decide +kernel
theorem s162_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 1 = true := by decide +kernel
theorem s162_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 2 = true := by decide +kernel
theorem s162_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 3 = true := by decide +kernel
theorem s162_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 4 = true := by decide +kernel
theorem s162_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 5 = true := by decide +kernel
theorem k162_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k162_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k162_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k162_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k162_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k162_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s162_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k162_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k162_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k162_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k162_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k162_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 162) ((InDA2.TCasaD 5 5 6).getD (162 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k162_5_6_50 k h.1 (by omega)
theorem s162_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 5 7 = true := by decide +kernel
theorem col162_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 6 v) = true := by decide +kernel
theorem col162_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 7 v) = true := by decide +kernel
theorem col162 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 162) 162 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col162_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col162_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s162_2_0
    · exact s162_2_1
    · exact s162_2_2
    · exact s162_2_3
    · exact s162_2_4
    · exact s162_2_5
    · exact s162_2_6
    · exact s162_2_7
  · fin_cases v
    · exact s162_3_0
    · exact s162_3_1
    · exact s162_3_2
    · exact s162_3_3
    · exact s162_3_4
    · exact s162_3_5
    · exact s162_3_6
    · exact s162_3_7
  · fin_cases v
    · exact s162_4_0
    · exact s162_4_1
    · exact s162_4_2
    · exact s162_4_3
    · exact s162_4_4
    · exact s162_4_5
    · exact s162_4_6
    · exact s162_4_7
  · fin_cases v
    · exact s162_5_0
    · exact s162_5_1
    · exact s162_5_2
    · exact s162_5_3
    · exact s162_5_4
    · exact s162_5_5
    · exact s162_5_6
    · exact s162_5_7
  · exact List.all_eq_true.mp col162_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col162_7 v (List.mem_finRange v)
theorem col163_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 0 v) = true := by decide +kernel
theorem col163_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 1 v) = true := by decide +kernel
theorem s163_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 0 = true := by decide +kernel
theorem s163_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 1 = true := by decide +kernel
theorem s163_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 2 = true := by decide +kernel
theorem s163_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 3 = true := by decide +kernel
theorem k163_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k163_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k163_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s163_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k163_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k163_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k163_2_4_80 k h.1 (by omega)
theorem s163_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 5 = true := by decide +kernel
theorem s163_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 6 = true := by decide +kernel
theorem s163_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 2 7 = true := by decide +kernel
theorem s163_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 0 = true := by decide +kernel
theorem s163_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 1 = true := by decide +kernel
theorem s163_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 2 = true := by decide +kernel
theorem s163_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 3 = true := by decide +kernel
theorem k163_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k163_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k163_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s163_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k163_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k163_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k163_3_4_80 k h.1 (by omega)
theorem s163_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 5 = true := by decide +kernel
theorem s163_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 6 = true := by decide +kernel
theorem s163_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 3 7 = true := by decide +kernel
theorem s163_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 0 = true := by decide +kernel
theorem s163_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 1 = true := by decide +kernel
theorem s163_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 2 = true := by decide +kernel
theorem s163_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 3 = true := by decide +kernel
theorem k163_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k163_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k163_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k163_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k163_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k163_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k163_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k163_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k163_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k163_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k163_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k163_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k163_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k163_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k163_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k163_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k163_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k163_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k163_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k163_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k163_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s163_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k163_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k163_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k163_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k163_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k163_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k163_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k163_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k163_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k163_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k163_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k163_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k163_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k163_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k163_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k163_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k163_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k163_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k163_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k163_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k163_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k163_4_4_100 k h.1 (by omega)
theorem k163_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k163_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k163_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k163_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k163_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k163_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k163_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k163_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k163_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s163_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k163_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k163_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k163_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k163_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k163_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k163_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k163_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k163_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 163) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (163 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k163_4_5_40 k h.1 (by omega)
theorem k163_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k163_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k163_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k163_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k163_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k163_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k163_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k163_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k163_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k163_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k163_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s163_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k163_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k163_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k163_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k163_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k163_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k163_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k163_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k163_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k163_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k163_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TTsaaD 4 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k163_4_6_50 k h.1 (by omega)
theorem s163_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 4 7 = true := by decide +kernel
theorem s163_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 0 = true := by decide +kernel
theorem s163_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 1 = true := by decide +kernel
theorem s163_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 2 = true := by decide +kernel
theorem s163_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 3 = true := by decide +kernel
theorem s163_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 4 = true := by decide +kernel
theorem s163_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 5 = true := by decide +kernel
theorem k163_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k163_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k163_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k163_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k163_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k163_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s163_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k163_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k163_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k163_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k163_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k163_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 163) ((InDA2.TCasaD 5 5 6).getD (163 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k163_5_6_50 k h.1 (by omega)
theorem s163_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 5 7 = true := by decide +kernel
theorem col163_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 6 v) = true := by decide +kernel
theorem col163_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 7 v) = true := by decide +kernel
theorem col163 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 163) 163 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col163_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col163_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s163_2_0
    · exact s163_2_1
    · exact s163_2_2
    · exact s163_2_3
    · exact s163_2_4
    · exact s163_2_5
    · exact s163_2_6
    · exact s163_2_7
  · fin_cases v
    · exact s163_3_0
    · exact s163_3_1
    · exact s163_3_2
    · exact s163_3_3
    · exact s163_3_4
    · exact s163_3_5
    · exact s163_3_6
    · exact s163_3_7
  · fin_cases v
    · exact s163_4_0
    · exact s163_4_1
    · exact s163_4_2
    · exact s163_4_3
    · exact s163_4_4
    · exact s163_4_5
    · exact s163_4_6
    · exact s163_4_7
  · fin_cases v
    · exact s163_5_0
    · exact s163_5_1
    · exact s163_5_2
    · exact s163_5_3
    · exact s163_5_4
    · exact s163_5_5
    · exact s163_5_6
    · exact s163_5_7
  · exact List.all_eq_true.mp col163_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col163_7 v (List.mem_finRange v)
theorem col164_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 0 v) = true := by decide +kernel
theorem col164_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 1 v) = true := by decide +kernel
theorem s164_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 0 = true := by decide +kernel
theorem s164_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 1 = true := by decide +kernel
theorem s164_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 2 = true := by decide +kernel
theorem s164_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 3 = true := by decide +kernel
theorem k164_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k164_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k164_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s164_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k164_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k164_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k164_2_4_80 k h.1 (by omega)
theorem s164_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 5 = true := by decide +kernel
theorem s164_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 6 = true := by decide +kernel
theorem s164_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 2 7 = true := by decide +kernel
theorem s164_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 0 = true := by decide +kernel
theorem s164_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 1 = true := by decide +kernel
theorem s164_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 2 = true := by decide +kernel
theorem s164_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 3 = true := by decide +kernel
theorem k164_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k164_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k164_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s164_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k164_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k164_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k164_3_4_80 k h.1 (by omega)
theorem s164_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 5 = true := by decide +kernel
theorem s164_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 6 = true := by decide +kernel
theorem s164_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 3 7 = true := by decide +kernel
theorem s164_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 0 = true := by decide +kernel
theorem s164_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 1 = true := by decide +kernel
theorem s164_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 2 = true := by decide +kernel
theorem s164_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 3 = true := by decide +kernel
theorem k164_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k164_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k164_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k164_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k164_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k164_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k164_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k164_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k164_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k164_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k164_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k164_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k164_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k164_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k164_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k164_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k164_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k164_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k164_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k164_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k164_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s164_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k164_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k164_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k164_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k164_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k164_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k164_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k164_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k164_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k164_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k164_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k164_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k164_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k164_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k164_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k164_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k164_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k164_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k164_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k164_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k164_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k164_4_4_100 k h.1 (by omega)
theorem k164_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k164_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k164_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k164_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k164_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k164_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k164_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k164_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k164_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s164_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k164_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k164_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k164_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k164_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k164_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k164_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k164_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k164_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 164) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (164 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k164_4_5_40 k h.1 (by omega)
theorem k164_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k164_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k164_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k164_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k164_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k164_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k164_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k164_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k164_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k164_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k164_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s164_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k164_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k164_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k164_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k164_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k164_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k164_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k164_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k164_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k164_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k164_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TTsaaD 4 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k164_4_6_50 k h.1 (by omega)
theorem s164_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 4 7 = true := by decide +kernel
theorem s164_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 0 = true := by decide +kernel
theorem s164_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 1 = true := by decide +kernel
theorem s164_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 2 = true := by decide +kernel
theorem s164_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 3 = true := by decide +kernel
theorem s164_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 4 = true := by decide +kernel
theorem s164_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 5 = true := by decide +kernel
theorem k164_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k164_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k164_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k164_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k164_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k164_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s164_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k164_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k164_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k164_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k164_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k164_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 164) ((InDA2.TCasaD 5 5 6).getD (164 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k164_5_6_50 k h.1 (by omega)
theorem s164_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 5 7 = true := by decide +kernel
theorem col164_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 6 v) = true := by decide +kernel
theorem col164_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 7 v) = true := by decide +kernel
theorem col164 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 164) 164 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col164_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col164_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s164_2_0
    · exact s164_2_1
    · exact s164_2_2
    · exact s164_2_3
    · exact s164_2_4
    · exact s164_2_5
    · exact s164_2_6
    · exact s164_2_7
  · fin_cases v
    · exact s164_3_0
    · exact s164_3_1
    · exact s164_3_2
    · exact s164_3_3
    · exact s164_3_4
    · exact s164_3_5
    · exact s164_3_6
    · exact s164_3_7
  · fin_cases v
    · exact s164_4_0
    · exact s164_4_1
    · exact s164_4_2
    · exact s164_4_3
    · exact s164_4_4
    · exact s164_4_5
    · exact s164_4_6
    · exact s164_4_7
  · fin_cases v
    · exact s164_5_0
    · exact s164_5_1
    · exact s164_5_2
    · exact s164_5_3
    · exact s164_5_4
    · exact s164_5_5
    · exact s164_5_6
    · exact s164_5_7
  · exact List.all_eq_true.mp col164_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col164_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
