module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [135, 140). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col135_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 0 v) = true := by decide +kernel
theorem col135_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 1 v) = true := by decide +kernel
theorem s135_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 0 = true := by decide +kernel
theorem s135_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 1 = true := by decide +kernel
theorem s135_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 2 = true := by decide +kernel
theorem s135_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 3 = true := by decide +kernel
theorem k135_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k135_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k135_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s135_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k135_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k135_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k135_2_4_80 k h.1 (by omega)
theorem s135_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 5 = true := by decide +kernel
theorem s135_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 6 = true := by decide +kernel
theorem s135_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 2 7 = true := by decide +kernel
theorem s135_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 0 = true := by decide +kernel
theorem s135_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 1 = true := by decide +kernel
theorem s135_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 2 = true := by decide +kernel
theorem s135_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 3 = true := by decide +kernel
theorem k135_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k135_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k135_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s135_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k135_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k135_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k135_3_4_80 k h.1 (by omega)
theorem s135_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 5 = true := by decide +kernel
theorem s135_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 6 = true := by decide +kernel
theorem s135_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 3 7 = true := by decide +kernel
theorem s135_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 0 = true := by decide +kernel
theorem s135_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 1 = true := by decide +kernel
theorem s135_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 2 = true := by decide +kernel
theorem s135_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 3 = true := by decide +kernel
theorem k135_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k135_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k135_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k135_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k135_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k135_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k135_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k135_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k135_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k135_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k135_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k135_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k135_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k135_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k135_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k135_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k135_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k135_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k135_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k135_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k135_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s135_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k135_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k135_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k135_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k135_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k135_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k135_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k135_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k135_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k135_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k135_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k135_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k135_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k135_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k135_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k135_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k135_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k135_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k135_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k135_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k135_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k135_4_4_100 k h.1 (by omega)
theorem k135_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k135_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k135_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k135_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k135_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k135_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k135_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k135_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k135_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s135_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k135_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k135_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k135_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k135_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k135_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k135_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k135_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k135_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 135) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (135 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k135_4_5_40 k h.1 (by omega)
theorem k135_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k135_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k135_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k135_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k135_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k135_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k135_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k135_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k135_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k135_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k135_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s135_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k135_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k135_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k135_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k135_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k135_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k135_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k135_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k135_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k135_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k135_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TTsaaD 4 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k135_4_6_50 k h.1 (by omega)
theorem s135_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 4 7 = true := by decide +kernel
theorem s135_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 0 = true := by decide +kernel
theorem s135_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 1 = true := by decide +kernel
theorem s135_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 2 = true := by decide +kernel
theorem s135_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 3 = true := by decide +kernel
theorem s135_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 4 = true := by decide +kernel
theorem s135_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 5 = true := by decide +kernel
theorem k135_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k135_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k135_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k135_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k135_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k135_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s135_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k135_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k135_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k135_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k135_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k135_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 135) ((InDA2.TCasaD 5 5 6).getD (135 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k135_5_6_50 k h.1 (by omega)
theorem s135_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 5 7 = true := by decide +kernel
theorem col135_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 6 v) = true := by decide +kernel
theorem col135_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 7 v) = true := by decide +kernel
theorem col135 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 135) 135 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col135_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col135_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s135_2_0
    · exact s135_2_1
    · exact s135_2_2
    · exact s135_2_3
    · exact s135_2_4
    · exact s135_2_5
    · exact s135_2_6
    · exact s135_2_7
  · fin_cases v
    · exact s135_3_0
    · exact s135_3_1
    · exact s135_3_2
    · exact s135_3_3
    · exact s135_3_4
    · exact s135_3_5
    · exact s135_3_6
    · exact s135_3_7
  · fin_cases v
    · exact s135_4_0
    · exact s135_4_1
    · exact s135_4_2
    · exact s135_4_3
    · exact s135_4_4
    · exact s135_4_5
    · exact s135_4_6
    · exact s135_4_7
  · fin_cases v
    · exact s135_5_0
    · exact s135_5_1
    · exact s135_5_2
    · exact s135_5_3
    · exact s135_5_4
    · exact s135_5_5
    · exact s135_5_6
    · exact s135_5_7
  · exact List.all_eq_true.mp col135_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col135_7 v (List.mem_finRange v)
theorem col136_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 0 v) = true := by decide +kernel
theorem col136_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 1 v) = true := by decide +kernel
theorem s136_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 0 = true := by decide +kernel
theorem s136_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 1 = true := by decide +kernel
theorem s136_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 2 = true := by decide +kernel
theorem s136_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 3 = true := by decide +kernel
theorem k136_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k136_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k136_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s136_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k136_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k136_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k136_2_4_80 k h.1 (by omega)
theorem s136_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 5 = true := by decide +kernel
theorem s136_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 6 = true := by decide +kernel
theorem s136_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 2 7 = true := by decide +kernel
theorem s136_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 0 = true := by decide +kernel
theorem s136_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 1 = true := by decide +kernel
theorem s136_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 2 = true := by decide +kernel
theorem s136_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 3 = true := by decide +kernel
theorem k136_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k136_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k136_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s136_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k136_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k136_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k136_3_4_80 k h.1 (by omega)
theorem s136_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 5 = true := by decide +kernel
theorem s136_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 6 = true := by decide +kernel
theorem s136_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 3 7 = true := by decide +kernel
theorem s136_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 0 = true := by decide +kernel
theorem s136_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 1 = true := by decide +kernel
theorem s136_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 2 = true := by decide +kernel
theorem s136_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 3 = true := by decide +kernel
theorem k136_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k136_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k136_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k136_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k136_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k136_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k136_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k136_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k136_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k136_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k136_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k136_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k136_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k136_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k136_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k136_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k136_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k136_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k136_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k136_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k136_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s136_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k136_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k136_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k136_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k136_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k136_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k136_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k136_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k136_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k136_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k136_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k136_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k136_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k136_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k136_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k136_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k136_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k136_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k136_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k136_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k136_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k136_4_4_100 k h.1 (by omega)
theorem k136_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k136_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k136_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k136_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k136_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k136_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k136_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k136_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k136_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s136_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k136_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k136_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k136_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k136_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k136_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k136_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k136_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k136_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 136) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (136 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k136_4_5_40 k h.1 (by omega)
theorem k136_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k136_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k136_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k136_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k136_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k136_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k136_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k136_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k136_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k136_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k136_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s136_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k136_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k136_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k136_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k136_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k136_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k136_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k136_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k136_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k136_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k136_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TTsaaD 4 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k136_4_6_50 k h.1 (by omega)
theorem s136_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 4 7 = true := by decide +kernel
theorem s136_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 0 = true := by decide +kernel
theorem s136_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 1 = true := by decide +kernel
theorem s136_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 2 = true := by decide +kernel
theorem s136_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 3 = true := by decide +kernel
theorem s136_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 4 = true := by decide +kernel
theorem s136_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 5 = true := by decide +kernel
theorem k136_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k136_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k136_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k136_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k136_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k136_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s136_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k136_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k136_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k136_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k136_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k136_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 136) ((InDA2.TCasaD 5 5 6).getD (136 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k136_5_6_50 k h.1 (by omega)
theorem s136_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 5 7 = true := by decide +kernel
theorem col136_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 6 v) = true := by decide +kernel
theorem col136_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 7 v) = true := by decide +kernel
theorem col136 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 136) 136 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col136_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col136_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s136_2_0
    · exact s136_2_1
    · exact s136_2_2
    · exact s136_2_3
    · exact s136_2_4
    · exact s136_2_5
    · exact s136_2_6
    · exact s136_2_7
  · fin_cases v
    · exact s136_3_0
    · exact s136_3_1
    · exact s136_3_2
    · exact s136_3_3
    · exact s136_3_4
    · exact s136_3_5
    · exact s136_3_6
    · exact s136_3_7
  · fin_cases v
    · exact s136_4_0
    · exact s136_4_1
    · exact s136_4_2
    · exact s136_4_3
    · exact s136_4_4
    · exact s136_4_5
    · exact s136_4_6
    · exact s136_4_7
  · fin_cases v
    · exact s136_5_0
    · exact s136_5_1
    · exact s136_5_2
    · exact s136_5_3
    · exact s136_5_4
    · exact s136_5_5
    · exact s136_5_6
    · exact s136_5_7
  · exact List.all_eq_true.mp col136_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col136_7 v (List.mem_finRange v)
theorem col137_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 0 v) = true := by decide +kernel
theorem col137_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 1 v) = true := by decide +kernel
theorem s137_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 0 = true := by decide +kernel
theorem s137_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 1 = true := by decide +kernel
theorem s137_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 2 = true := by decide +kernel
theorem s137_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 3 = true := by decide +kernel
theorem k137_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k137_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k137_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s137_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k137_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k137_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k137_2_4_80 k h.1 (by omega)
theorem s137_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 5 = true := by decide +kernel
theorem s137_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 6 = true := by decide +kernel
theorem s137_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 2 7 = true := by decide +kernel
theorem s137_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 0 = true := by decide +kernel
theorem s137_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 1 = true := by decide +kernel
theorem s137_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 2 = true := by decide +kernel
theorem s137_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 3 = true := by decide +kernel
theorem k137_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k137_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k137_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s137_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k137_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k137_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k137_3_4_80 k h.1 (by omega)
theorem s137_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 5 = true := by decide +kernel
theorem s137_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 6 = true := by decide +kernel
theorem s137_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 3 7 = true := by decide +kernel
theorem s137_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 0 = true := by decide +kernel
theorem s137_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 1 = true := by decide +kernel
theorem s137_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 2 = true := by decide +kernel
theorem s137_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 3 = true := by decide +kernel
theorem k137_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k137_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k137_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k137_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k137_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k137_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k137_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k137_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k137_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k137_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k137_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k137_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k137_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k137_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k137_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k137_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k137_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k137_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k137_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k137_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k137_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s137_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k137_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k137_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k137_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k137_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k137_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k137_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k137_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k137_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k137_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k137_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k137_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k137_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k137_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k137_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k137_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k137_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k137_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k137_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k137_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k137_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k137_4_4_100 k h.1 (by omega)
theorem k137_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k137_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k137_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k137_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k137_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k137_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k137_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k137_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k137_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s137_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k137_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k137_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k137_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k137_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k137_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k137_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k137_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k137_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 137) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (137 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k137_4_5_40 k h.1 (by omega)
theorem k137_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k137_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k137_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k137_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k137_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k137_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k137_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k137_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k137_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k137_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k137_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s137_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k137_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k137_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k137_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k137_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k137_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k137_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k137_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k137_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k137_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k137_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TTsaaD 4 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k137_4_6_50 k h.1 (by omega)
theorem s137_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 4 7 = true := by decide +kernel
theorem s137_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 0 = true := by decide +kernel
theorem s137_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 1 = true := by decide +kernel
theorem s137_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 2 = true := by decide +kernel
theorem s137_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 3 = true := by decide +kernel
theorem s137_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 4 = true := by decide +kernel
theorem s137_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 5 = true := by decide +kernel
theorem k137_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k137_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k137_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k137_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k137_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k137_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s137_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k137_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k137_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k137_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k137_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k137_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 137) ((InDA2.TCasaD 5 5 6).getD (137 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k137_5_6_50 k h.1 (by omega)
theorem s137_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 5 7 = true := by decide +kernel
theorem col137_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 6 v) = true := by decide +kernel
theorem col137_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 7 v) = true := by decide +kernel
theorem col137 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 137) 137 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col137_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col137_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s137_2_0
    · exact s137_2_1
    · exact s137_2_2
    · exact s137_2_3
    · exact s137_2_4
    · exact s137_2_5
    · exact s137_2_6
    · exact s137_2_7
  · fin_cases v
    · exact s137_3_0
    · exact s137_3_1
    · exact s137_3_2
    · exact s137_3_3
    · exact s137_3_4
    · exact s137_3_5
    · exact s137_3_6
    · exact s137_3_7
  · fin_cases v
    · exact s137_4_0
    · exact s137_4_1
    · exact s137_4_2
    · exact s137_4_3
    · exact s137_4_4
    · exact s137_4_5
    · exact s137_4_6
    · exact s137_4_7
  · fin_cases v
    · exact s137_5_0
    · exact s137_5_1
    · exact s137_5_2
    · exact s137_5_3
    · exact s137_5_4
    · exact s137_5_5
    · exact s137_5_6
    · exact s137_5_7
  · exact List.all_eq_true.mp col137_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col137_7 v (List.mem_finRange v)
theorem col138_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 0 v) = true := by decide +kernel
theorem col138_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 1 v) = true := by decide +kernel
theorem s138_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 0 = true := by decide +kernel
theorem s138_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 1 = true := by decide +kernel
theorem s138_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 2 = true := by decide +kernel
theorem s138_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 3 = true := by decide +kernel
theorem k138_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k138_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k138_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s138_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k138_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k138_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k138_2_4_80 k h.1 (by omega)
theorem s138_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 5 = true := by decide +kernel
theorem s138_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 6 = true := by decide +kernel
theorem s138_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 2 7 = true := by decide +kernel
theorem s138_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 0 = true := by decide +kernel
theorem s138_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 1 = true := by decide +kernel
theorem s138_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 2 = true := by decide +kernel
theorem s138_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 3 = true := by decide +kernel
theorem k138_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k138_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k138_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s138_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k138_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k138_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k138_3_4_80 k h.1 (by omega)
theorem s138_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 5 = true := by decide +kernel
theorem s138_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 6 = true := by decide +kernel
theorem s138_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 3 7 = true := by decide +kernel
theorem s138_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 0 = true := by decide +kernel
theorem s138_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 1 = true := by decide +kernel
theorem s138_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 2 = true := by decide +kernel
theorem s138_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 3 = true := by decide +kernel
theorem k138_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k138_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k138_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k138_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k138_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k138_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k138_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k138_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k138_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k138_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k138_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k138_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k138_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k138_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k138_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k138_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k138_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k138_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k138_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k138_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k138_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s138_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k138_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k138_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k138_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k138_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k138_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k138_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k138_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k138_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k138_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k138_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k138_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k138_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k138_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k138_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k138_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k138_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k138_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k138_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k138_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k138_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k138_4_4_100 k h.1 (by omega)
theorem k138_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k138_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k138_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k138_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k138_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k138_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k138_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k138_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k138_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s138_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k138_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k138_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k138_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k138_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k138_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k138_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k138_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k138_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 138) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (138 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k138_4_5_40 k h.1 (by omega)
theorem k138_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k138_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k138_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k138_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k138_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k138_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k138_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k138_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k138_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k138_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k138_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s138_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k138_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k138_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k138_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k138_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k138_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k138_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k138_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k138_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k138_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k138_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TTsaaD 4 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k138_4_6_50 k h.1 (by omega)
theorem s138_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 4 7 = true := by decide +kernel
theorem s138_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 0 = true := by decide +kernel
theorem s138_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 1 = true := by decide +kernel
theorem s138_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 2 = true := by decide +kernel
theorem s138_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 3 = true := by decide +kernel
theorem s138_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 4 = true := by decide +kernel
theorem s138_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 5 = true := by decide +kernel
theorem k138_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k138_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k138_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k138_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k138_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k138_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s138_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k138_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k138_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k138_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k138_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k138_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 138) ((InDA2.TCasaD 5 5 6).getD (138 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k138_5_6_50 k h.1 (by omega)
theorem s138_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 5 7 = true := by decide +kernel
theorem col138_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 6 v) = true := by decide +kernel
theorem col138_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 7 v) = true := by decide +kernel
theorem col138 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 138) 138 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col138_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col138_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s138_2_0
    · exact s138_2_1
    · exact s138_2_2
    · exact s138_2_3
    · exact s138_2_4
    · exact s138_2_5
    · exact s138_2_6
    · exact s138_2_7
  · fin_cases v
    · exact s138_3_0
    · exact s138_3_1
    · exact s138_3_2
    · exact s138_3_3
    · exact s138_3_4
    · exact s138_3_5
    · exact s138_3_6
    · exact s138_3_7
  · fin_cases v
    · exact s138_4_0
    · exact s138_4_1
    · exact s138_4_2
    · exact s138_4_3
    · exact s138_4_4
    · exact s138_4_5
    · exact s138_4_6
    · exact s138_4_7
  · fin_cases v
    · exact s138_5_0
    · exact s138_5_1
    · exact s138_5_2
    · exact s138_5_3
    · exact s138_5_4
    · exact s138_5_5
    · exact s138_5_6
    · exact s138_5_7
  · exact List.all_eq_true.mp col138_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col138_7 v (List.mem_finRange v)
theorem col139_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 0 v) = true := by decide +kernel
theorem col139_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 1 v) = true := by decide +kernel
theorem s139_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 0 = true := by decide +kernel
theorem s139_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 1 = true := by decide +kernel
theorem s139_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 2 = true := by decide +kernel
theorem s139_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 3 = true := by decide +kernel
theorem k139_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k139_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k139_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s139_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k139_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k139_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k139_2_4_80 k h.1 (by omega)
theorem s139_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 5 = true := by decide +kernel
theorem s139_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 6 = true := by decide +kernel
theorem s139_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 2 7 = true := by decide +kernel
theorem s139_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 0 = true := by decide +kernel
theorem s139_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 1 = true := by decide +kernel
theorem s139_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 2 = true := by decide +kernel
theorem s139_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 3 = true := by decide +kernel
theorem k139_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k139_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k139_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s139_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k139_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k139_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k139_3_4_80 k h.1 (by omega)
theorem s139_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 5 = true := by decide +kernel
theorem s139_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 6 = true := by decide +kernel
theorem s139_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 3 7 = true := by decide +kernel
theorem s139_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 0 = true := by decide +kernel
theorem s139_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 1 = true := by decide +kernel
theorem s139_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 2 = true := by decide +kernel
theorem s139_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 3 = true := by decide +kernel
theorem k139_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k139_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k139_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k139_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k139_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k139_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k139_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k139_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k139_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k139_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k139_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k139_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k139_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k139_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k139_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k139_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k139_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k139_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k139_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k139_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k139_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s139_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k139_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k139_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k139_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k139_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k139_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k139_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k139_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k139_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k139_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k139_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k139_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k139_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k139_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k139_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k139_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k139_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k139_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k139_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k139_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k139_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k139_4_4_100 k h.1 (by omega)
theorem k139_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k139_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k139_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k139_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k139_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k139_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k139_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k139_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k139_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s139_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k139_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k139_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k139_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k139_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k139_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k139_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k139_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k139_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 139) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (139 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k139_4_5_40 k h.1 (by omega)
theorem k139_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k139_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k139_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k139_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k139_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k139_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k139_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k139_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k139_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k139_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k139_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s139_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k139_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k139_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k139_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k139_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k139_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k139_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k139_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k139_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k139_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k139_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TTsaaD 4 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k139_4_6_50 k h.1 (by omega)
theorem s139_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 4 7 = true := by decide +kernel
theorem s139_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 0 = true := by decide +kernel
theorem s139_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 1 = true := by decide +kernel
theorem s139_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 2 = true := by decide +kernel
theorem s139_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 3 = true := by decide +kernel
theorem s139_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 4 = true := by decide +kernel
theorem s139_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 5 = true := by decide +kernel
theorem k139_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k139_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k139_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k139_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k139_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k139_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s139_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k139_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k139_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k139_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k139_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k139_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 139) ((InDA2.TCasaD 5 5 6).getD (139 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k139_5_6_50 k h.1 (by omega)
theorem s139_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 5 7 = true := by decide +kernel
theorem col139_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 6 v) = true := by decide +kernel
theorem col139_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 7 v) = true := by decide +kernel
theorem col139 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 139) 139 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col139_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col139_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s139_2_0
    · exact s139_2_1
    · exact s139_2_2
    · exact s139_2_3
    · exact s139_2_4
    · exact s139_2_5
    · exact s139_2_6
    · exact s139_2_7
  · fin_cases v
    · exact s139_3_0
    · exact s139_3_1
    · exact s139_3_2
    · exact s139_3_3
    · exact s139_3_4
    · exact s139_3_5
    · exact s139_3_6
    · exact s139_3_7
  · fin_cases v
    · exact s139_4_0
    · exact s139_4_1
    · exact s139_4_2
    · exact s139_4_3
    · exact s139_4_4
    · exact s139_4_5
    · exact s139_4_6
    · exact s139_4_7
  · fin_cases v
    · exact s139_5_0
    · exact s139_5_1
    · exact s139_5_2
    · exact s139_5_3
    · exact s139_5_4
    · exact s139_5_5
    · exact s139_5_6
    · exact s139_5_7
  · exact List.all_eq_true.mp col139_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col139_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
