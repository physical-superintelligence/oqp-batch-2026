module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [150, 155). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col150_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 0 v) = true := by decide +kernel
theorem col150_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 1 v) = true := by decide +kernel
theorem s150_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 0 = true := by decide +kernel
theorem s150_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 1 = true := by decide +kernel
theorem s150_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 2 = true := by decide +kernel
theorem s150_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 3 = true := by decide +kernel
theorem k150_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k150_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k150_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s150_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k150_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k150_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k150_2_4_80 k h.1 (by omega)
theorem s150_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 5 = true := by decide +kernel
theorem s150_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 6 = true := by decide +kernel
theorem s150_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 2 7 = true := by decide +kernel
theorem s150_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 0 = true := by decide +kernel
theorem s150_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 1 = true := by decide +kernel
theorem s150_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 2 = true := by decide +kernel
theorem s150_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 3 = true := by decide +kernel
theorem k150_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k150_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k150_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s150_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k150_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k150_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k150_3_4_80 k h.1 (by omega)
theorem s150_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 5 = true := by decide +kernel
theorem s150_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 6 = true := by decide +kernel
theorem s150_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 3 7 = true := by decide +kernel
theorem s150_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 0 = true := by decide +kernel
theorem s150_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 1 = true := by decide +kernel
theorem s150_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 2 = true := by decide +kernel
theorem s150_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 3 = true := by decide +kernel
theorem k150_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k150_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k150_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k150_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k150_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k150_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k150_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k150_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k150_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k150_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k150_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k150_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k150_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k150_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k150_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k150_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k150_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k150_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k150_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k150_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k150_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s150_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k150_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k150_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k150_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k150_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k150_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k150_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k150_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k150_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k150_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k150_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k150_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k150_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k150_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k150_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k150_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k150_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k150_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k150_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k150_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k150_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k150_4_4_100 k h.1 (by omega)
theorem k150_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k150_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k150_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k150_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k150_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k150_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k150_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k150_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k150_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s150_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k150_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k150_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k150_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k150_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k150_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k150_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k150_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k150_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 150) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (150 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k150_4_5_40 k h.1 (by omega)
theorem k150_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k150_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k150_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k150_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k150_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k150_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k150_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k150_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k150_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k150_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k150_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s150_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k150_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k150_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k150_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k150_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k150_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k150_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k150_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k150_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k150_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k150_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TTsaaD 4 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k150_4_6_50 k h.1 (by omega)
theorem s150_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 4 7 = true := by decide +kernel
theorem s150_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 0 = true := by decide +kernel
theorem s150_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 1 = true := by decide +kernel
theorem s150_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 2 = true := by decide +kernel
theorem s150_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 3 = true := by decide +kernel
theorem s150_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 4 = true := by decide +kernel
theorem s150_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 5 = true := by decide +kernel
theorem k150_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k150_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k150_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k150_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k150_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k150_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s150_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k150_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k150_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k150_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k150_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k150_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 150) ((InDA2.TCasaD 5 5 6).getD (150 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k150_5_6_50 k h.1 (by omega)
theorem s150_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 5 7 = true := by decide +kernel
theorem col150_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 6 v) = true := by decide +kernel
theorem col150_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 7 v) = true := by decide +kernel
theorem col150 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 150) 150 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col150_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col150_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s150_2_0
    · exact s150_2_1
    · exact s150_2_2
    · exact s150_2_3
    · exact s150_2_4
    · exact s150_2_5
    · exact s150_2_6
    · exact s150_2_7
  · fin_cases v
    · exact s150_3_0
    · exact s150_3_1
    · exact s150_3_2
    · exact s150_3_3
    · exact s150_3_4
    · exact s150_3_5
    · exact s150_3_6
    · exact s150_3_7
  · fin_cases v
    · exact s150_4_0
    · exact s150_4_1
    · exact s150_4_2
    · exact s150_4_3
    · exact s150_4_4
    · exact s150_4_5
    · exact s150_4_6
    · exact s150_4_7
  · fin_cases v
    · exact s150_5_0
    · exact s150_5_1
    · exact s150_5_2
    · exact s150_5_3
    · exact s150_5_4
    · exact s150_5_5
    · exact s150_5_6
    · exact s150_5_7
  · exact List.all_eq_true.mp col150_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col150_7 v (List.mem_finRange v)
theorem col151_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 0 v) = true := by decide +kernel
theorem col151_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 1 v) = true := by decide +kernel
theorem s151_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 0 = true := by decide +kernel
theorem s151_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 1 = true := by decide +kernel
theorem s151_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 2 = true := by decide +kernel
theorem s151_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 3 = true := by decide +kernel
theorem k151_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k151_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k151_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s151_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k151_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k151_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k151_2_4_80 k h.1 (by omega)
theorem s151_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 5 = true := by decide +kernel
theorem s151_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 6 = true := by decide +kernel
theorem s151_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 2 7 = true := by decide +kernel
theorem s151_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 0 = true := by decide +kernel
theorem s151_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 1 = true := by decide +kernel
theorem s151_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 2 = true := by decide +kernel
theorem s151_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 3 = true := by decide +kernel
theorem k151_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k151_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k151_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s151_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k151_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k151_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k151_3_4_80 k h.1 (by omega)
theorem s151_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 5 = true := by decide +kernel
theorem s151_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 6 = true := by decide +kernel
theorem s151_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 3 7 = true := by decide +kernel
theorem s151_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 0 = true := by decide +kernel
theorem s151_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 1 = true := by decide +kernel
theorem s151_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 2 = true := by decide +kernel
theorem s151_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 3 = true := by decide +kernel
theorem k151_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k151_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k151_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k151_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k151_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k151_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k151_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k151_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k151_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k151_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k151_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k151_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k151_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k151_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k151_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k151_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k151_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k151_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k151_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k151_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k151_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s151_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k151_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k151_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k151_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k151_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k151_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k151_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k151_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k151_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k151_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k151_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k151_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k151_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k151_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k151_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k151_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k151_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k151_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k151_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k151_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k151_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k151_4_4_100 k h.1 (by omega)
theorem k151_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k151_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k151_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k151_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k151_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k151_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k151_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k151_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k151_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s151_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k151_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k151_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k151_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k151_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k151_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k151_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k151_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k151_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 151) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (151 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k151_4_5_40 k h.1 (by omega)
theorem k151_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k151_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k151_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k151_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k151_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k151_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k151_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k151_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k151_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k151_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k151_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s151_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k151_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k151_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k151_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k151_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k151_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k151_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k151_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k151_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k151_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k151_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TTsaaD 4 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k151_4_6_50 k h.1 (by omega)
theorem s151_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 4 7 = true := by decide +kernel
theorem s151_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 0 = true := by decide +kernel
theorem s151_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 1 = true := by decide +kernel
theorem s151_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 2 = true := by decide +kernel
theorem s151_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 3 = true := by decide +kernel
theorem s151_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 4 = true := by decide +kernel
theorem s151_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 5 = true := by decide +kernel
theorem k151_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k151_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k151_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k151_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k151_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k151_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s151_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k151_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k151_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k151_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k151_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k151_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 151) ((InDA2.TCasaD 5 5 6).getD (151 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k151_5_6_50 k h.1 (by omega)
theorem s151_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 5 7 = true := by decide +kernel
theorem col151_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 6 v) = true := by decide +kernel
theorem col151_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 7 v) = true := by decide +kernel
theorem col151 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 151) 151 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col151_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col151_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s151_2_0
    · exact s151_2_1
    · exact s151_2_2
    · exact s151_2_3
    · exact s151_2_4
    · exact s151_2_5
    · exact s151_2_6
    · exact s151_2_7
  · fin_cases v
    · exact s151_3_0
    · exact s151_3_1
    · exact s151_3_2
    · exact s151_3_3
    · exact s151_3_4
    · exact s151_3_5
    · exact s151_3_6
    · exact s151_3_7
  · fin_cases v
    · exact s151_4_0
    · exact s151_4_1
    · exact s151_4_2
    · exact s151_4_3
    · exact s151_4_4
    · exact s151_4_5
    · exact s151_4_6
    · exact s151_4_7
  · fin_cases v
    · exact s151_5_0
    · exact s151_5_1
    · exact s151_5_2
    · exact s151_5_3
    · exact s151_5_4
    · exact s151_5_5
    · exact s151_5_6
    · exact s151_5_7
  · exact List.all_eq_true.mp col151_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col151_7 v (List.mem_finRange v)
theorem col152_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 0 v) = true := by decide +kernel
theorem col152_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 1 v) = true := by decide +kernel
theorem s152_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 0 = true := by decide +kernel
theorem s152_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 1 = true := by decide +kernel
theorem s152_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 2 = true := by decide +kernel
theorem s152_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 3 = true := by decide +kernel
theorem k152_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k152_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k152_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s152_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k152_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k152_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k152_2_4_80 k h.1 (by omega)
theorem s152_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 5 = true := by decide +kernel
theorem s152_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 6 = true := by decide +kernel
theorem s152_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 2 7 = true := by decide +kernel
theorem s152_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 0 = true := by decide +kernel
theorem s152_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 1 = true := by decide +kernel
theorem s152_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 2 = true := by decide +kernel
theorem s152_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 3 = true := by decide +kernel
theorem k152_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k152_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k152_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s152_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k152_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k152_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k152_3_4_80 k h.1 (by omega)
theorem s152_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 5 = true := by decide +kernel
theorem s152_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 6 = true := by decide +kernel
theorem s152_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 3 7 = true := by decide +kernel
theorem s152_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 0 = true := by decide +kernel
theorem s152_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 1 = true := by decide +kernel
theorem s152_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 2 = true := by decide +kernel
theorem s152_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 3 = true := by decide +kernel
theorem k152_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k152_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k152_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k152_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k152_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k152_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k152_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k152_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k152_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k152_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k152_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k152_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k152_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k152_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k152_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k152_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k152_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k152_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k152_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k152_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k152_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s152_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k152_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k152_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k152_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k152_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k152_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k152_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k152_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k152_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k152_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k152_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k152_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k152_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k152_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k152_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k152_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k152_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k152_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k152_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k152_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k152_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k152_4_4_100 k h.1 (by omega)
theorem k152_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k152_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k152_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k152_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k152_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k152_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k152_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k152_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k152_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s152_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k152_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k152_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k152_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k152_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k152_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k152_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k152_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k152_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 152) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (152 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k152_4_5_40 k h.1 (by omega)
theorem k152_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k152_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k152_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k152_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k152_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k152_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k152_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k152_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k152_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k152_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k152_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s152_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k152_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k152_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k152_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k152_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k152_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k152_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k152_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k152_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k152_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k152_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TTsaaD 4 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k152_4_6_50 k h.1 (by omega)
theorem s152_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 4 7 = true := by decide +kernel
theorem s152_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 0 = true := by decide +kernel
theorem s152_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 1 = true := by decide +kernel
theorem s152_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 2 = true := by decide +kernel
theorem s152_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 3 = true := by decide +kernel
theorem s152_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 4 = true := by decide +kernel
theorem s152_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 5 = true := by decide +kernel
theorem k152_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k152_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k152_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k152_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k152_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k152_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s152_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k152_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k152_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k152_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k152_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k152_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 152) ((InDA2.TCasaD 5 5 6).getD (152 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k152_5_6_50 k h.1 (by omega)
theorem s152_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 5 7 = true := by decide +kernel
theorem col152_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 6 v) = true := by decide +kernel
theorem col152_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 7 v) = true := by decide +kernel
theorem col152 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 152) 152 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col152_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col152_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s152_2_0
    · exact s152_2_1
    · exact s152_2_2
    · exact s152_2_3
    · exact s152_2_4
    · exact s152_2_5
    · exact s152_2_6
    · exact s152_2_7
  · fin_cases v
    · exact s152_3_0
    · exact s152_3_1
    · exact s152_3_2
    · exact s152_3_3
    · exact s152_3_4
    · exact s152_3_5
    · exact s152_3_6
    · exact s152_3_7
  · fin_cases v
    · exact s152_4_0
    · exact s152_4_1
    · exact s152_4_2
    · exact s152_4_3
    · exact s152_4_4
    · exact s152_4_5
    · exact s152_4_6
    · exact s152_4_7
  · fin_cases v
    · exact s152_5_0
    · exact s152_5_1
    · exact s152_5_2
    · exact s152_5_3
    · exact s152_5_4
    · exact s152_5_5
    · exact s152_5_6
    · exact s152_5_7
  · exact List.all_eq_true.mp col152_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col152_7 v (List.mem_finRange v)
theorem col153_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 0 v) = true := by decide +kernel
theorem col153_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 1 v) = true := by decide +kernel
theorem s153_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 0 = true := by decide +kernel
theorem s153_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 1 = true := by decide +kernel
theorem s153_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 2 = true := by decide +kernel
theorem s153_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 3 = true := by decide +kernel
theorem k153_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k153_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k153_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s153_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k153_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k153_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k153_2_4_80 k h.1 (by omega)
theorem s153_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 5 = true := by decide +kernel
theorem s153_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 6 = true := by decide +kernel
theorem s153_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 2 7 = true := by decide +kernel
theorem s153_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 0 = true := by decide +kernel
theorem s153_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 1 = true := by decide +kernel
theorem s153_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 2 = true := by decide +kernel
theorem s153_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 3 = true := by decide +kernel
theorem k153_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k153_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k153_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s153_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k153_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k153_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k153_3_4_80 k h.1 (by omega)
theorem s153_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 5 = true := by decide +kernel
theorem s153_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 6 = true := by decide +kernel
theorem s153_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 3 7 = true := by decide +kernel
theorem s153_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 0 = true := by decide +kernel
theorem s153_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 1 = true := by decide +kernel
theorem s153_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 2 = true := by decide +kernel
theorem s153_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 3 = true := by decide +kernel
theorem k153_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k153_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k153_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k153_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k153_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k153_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k153_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k153_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k153_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k153_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k153_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k153_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k153_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k153_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k153_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k153_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k153_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k153_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k153_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k153_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k153_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s153_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k153_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k153_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k153_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k153_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k153_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k153_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k153_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k153_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k153_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k153_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k153_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k153_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k153_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k153_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k153_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k153_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k153_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k153_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k153_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k153_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k153_4_4_100 k h.1 (by omega)
theorem k153_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k153_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k153_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k153_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k153_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k153_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k153_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k153_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k153_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s153_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k153_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k153_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k153_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k153_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k153_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k153_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k153_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k153_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 153) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (153 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k153_4_5_40 k h.1 (by omega)
theorem k153_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k153_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k153_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k153_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k153_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k153_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k153_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k153_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k153_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k153_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k153_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s153_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k153_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k153_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k153_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k153_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k153_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k153_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k153_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k153_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k153_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k153_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TTsaaD 4 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k153_4_6_50 k h.1 (by omega)
theorem s153_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 4 7 = true := by decide +kernel
theorem s153_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 0 = true := by decide +kernel
theorem s153_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 1 = true := by decide +kernel
theorem s153_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 2 = true := by decide +kernel
theorem s153_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 3 = true := by decide +kernel
theorem s153_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 4 = true := by decide +kernel
theorem s153_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 5 = true := by decide +kernel
theorem k153_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k153_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k153_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k153_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k153_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k153_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s153_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k153_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k153_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k153_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k153_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k153_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 153) ((InDA2.TCasaD 5 5 6).getD (153 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k153_5_6_50 k h.1 (by omega)
theorem s153_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 5 7 = true := by decide +kernel
theorem col153_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 6 v) = true := by decide +kernel
theorem col153_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 7 v) = true := by decide +kernel
theorem col153 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 153) 153 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col153_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col153_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s153_2_0
    · exact s153_2_1
    · exact s153_2_2
    · exact s153_2_3
    · exact s153_2_4
    · exact s153_2_5
    · exact s153_2_6
    · exact s153_2_7
  · fin_cases v
    · exact s153_3_0
    · exact s153_3_1
    · exact s153_3_2
    · exact s153_3_3
    · exact s153_3_4
    · exact s153_3_5
    · exact s153_3_6
    · exact s153_3_7
  · fin_cases v
    · exact s153_4_0
    · exact s153_4_1
    · exact s153_4_2
    · exact s153_4_3
    · exact s153_4_4
    · exact s153_4_5
    · exact s153_4_6
    · exact s153_4_7
  · fin_cases v
    · exact s153_5_0
    · exact s153_5_1
    · exact s153_5_2
    · exact s153_5_3
    · exact s153_5_4
    · exact s153_5_5
    · exact s153_5_6
    · exact s153_5_7
  · exact List.all_eq_true.mp col153_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col153_7 v (List.mem_finRange v)
theorem col154_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 0 v) = true := by decide +kernel
theorem col154_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 1 v) = true := by decide +kernel
theorem s154_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 0 = true := by decide +kernel
theorem s154_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 1 = true := by decide +kernel
theorem s154_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 2 = true := by decide +kernel
theorem s154_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 3 = true := by decide +kernel
theorem k154_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k154_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k154_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s154_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k154_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k154_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k154_2_4_80 k h.1 (by omega)
theorem s154_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 5 = true := by decide +kernel
theorem s154_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 6 = true := by decide +kernel
theorem s154_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 2 7 = true := by decide +kernel
theorem s154_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 0 = true := by decide +kernel
theorem s154_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 1 = true := by decide +kernel
theorem s154_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 2 = true := by decide +kernel
theorem s154_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 3 = true := by decide +kernel
theorem k154_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k154_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k154_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s154_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k154_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k154_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k154_3_4_80 k h.1 (by omega)
theorem s154_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 5 = true := by decide +kernel
theorem s154_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 6 = true := by decide +kernel
theorem s154_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 3 7 = true := by decide +kernel
theorem s154_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 0 = true := by decide +kernel
theorem s154_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 1 = true := by decide +kernel
theorem s154_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 2 = true := by decide +kernel
theorem s154_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 3 = true := by decide +kernel
theorem k154_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k154_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k154_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k154_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k154_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k154_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k154_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k154_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k154_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k154_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k154_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k154_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k154_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k154_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k154_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k154_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k154_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k154_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k154_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k154_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k154_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s154_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k154_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k154_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k154_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k154_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k154_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k154_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k154_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k154_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k154_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k154_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k154_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k154_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k154_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k154_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k154_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k154_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k154_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k154_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k154_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k154_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k154_4_4_100 k h.1 (by omega)
theorem k154_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k154_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k154_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k154_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k154_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k154_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k154_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k154_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k154_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s154_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k154_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k154_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k154_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k154_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k154_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k154_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k154_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k154_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 154) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (154 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k154_4_5_40 k h.1 (by omega)
theorem k154_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k154_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k154_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k154_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k154_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k154_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k154_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k154_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k154_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k154_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k154_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s154_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k154_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k154_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k154_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k154_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k154_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k154_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k154_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k154_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k154_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k154_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TTsaaD 4 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k154_4_6_50 k h.1 (by omega)
theorem s154_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 4 7 = true := by decide +kernel
theorem s154_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 0 = true := by decide +kernel
theorem s154_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 1 = true := by decide +kernel
theorem s154_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 2 = true := by decide +kernel
theorem s154_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 3 = true := by decide +kernel
theorem s154_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 4 = true := by decide +kernel
theorem s154_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 5 = true := by decide +kernel
theorem k154_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k154_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k154_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k154_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k154_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k154_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s154_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k154_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k154_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k154_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k154_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k154_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 154) ((InDA2.TCasaD 5 5 6).getD (154 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k154_5_6_50 k h.1 (by omega)
theorem s154_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 5 7 = true := by decide +kernel
theorem col154_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 6 v) = true := by decide +kernel
theorem col154_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 7 v) = true := by decide +kernel
theorem col154 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 154) 154 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col154_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col154_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s154_2_0
    · exact s154_2_1
    · exact s154_2_2
    · exact s154_2_3
    · exact s154_2_4
    · exact s154_2_5
    · exact s154_2_6
    · exact s154_2_7
  · fin_cases v
    · exact s154_3_0
    · exact s154_3_1
    · exact s154_3_2
    · exact s154_3_3
    · exact s154_3_4
    · exact s154_3_5
    · exact s154_3_6
    · exact s154_3_7
  · fin_cases v
    · exact s154_4_0
    · exact s154_4_1
    · exact s154_4_2
    · exact s154_4_3
    · exact s154_4_4
    · exact s154_4_5
    · exact s154_4_6
    · exact s154_4_7
  · fin_cases v
    · exact s154_5_0
    · exact s154_5_1
    · exact s154_5_2
    · exact s154_5_3
    · exact s154_5_4
    · exact s154_5_5
    · exact s154_5_6
    · exact s154_5_7
  · exact List.all_eq_true.mp col154_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col154_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
