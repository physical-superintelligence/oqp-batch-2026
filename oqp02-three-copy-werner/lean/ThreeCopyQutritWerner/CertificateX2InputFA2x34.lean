module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [170, 175). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col170_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 0 v) = true := by decide +kernel
theorem col170_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 1 v) = true := by decide +kernel
theorem s170_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 0 = true := by decide +kernel
theorem s170_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 1 = true := by decide +kernel
theorem s170_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 2 = true := by decide +kernel
theorem s170_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 3 = true := by decide +kernel
theorem k170_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k170_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k170_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s170_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k170_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k170_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k170_2_4_80 k h.1 (by omega)
theorem s170_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 5 = true := by decide +kernel
theorem s170_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 6 = true := by decide +kernel
theorem s170_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 2 7 = true := by decide +kernel
theorem s170_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 0 = true := by decide +kernel
theorem s170_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 1 = true := by decide +kernel
theorem s170_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 2 = true := by decide +kernel
theorem s170_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 3 = true := by decide +kernel
theorem k170_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k170_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k170_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s170_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k170_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k170_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k170_3_4_80 k h.1 (by omega)
theorem s170_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 5 = true := by decide +kernel
theorem s170_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 6 = true := by decide +kernel
theorem s170_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 3 7 = true := by decide +kernel
theorem s170_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 0 = true := by decide +kernel
theorem s170_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 1 = true := by decide +kernel
theorem s170_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 2 = true := by decide +kernel
theorem s170_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 3 = true := by decide +kernel
theorem k170_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k170_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k170_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k170_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k170_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k170_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k170_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k170_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k170_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k170_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k170_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k170_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k170_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k170_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k170_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k170_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k170_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k170_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k170_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k170_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k170_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s170_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k170_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k170_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k170_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k170_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k170_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k170_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k170_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k170_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k170_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k170_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k170_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k170_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k170_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k170_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k170_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k170_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k170_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k170_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k170_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k170_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k170_4_4_100 k h.1 (by omega)
theorem k170_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k170_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k170_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k170_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k170_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k170_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k170_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k170_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k170_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s170_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k170_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k170_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k170_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k170_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k170_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k170_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k170_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k170_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 170) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (170 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k170_4_5_40 k h.1 (by omega)
theorem k170_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k170_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k170_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k170_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k170_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k170_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k170_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k170_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k170_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k170_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k170_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s170_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k170_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k170_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k170_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k170_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k170_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k170_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k170_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k170_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k170_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k170_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TTsaaD 4 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k170_4_6_50 k h.1 (by omega)
theorem s170_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 4 7 = true := by decide +kernel
theorem s170_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 0 = true := by decide +kernel
theorem s170_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 1 = true := by decide +kernel
theorem s170_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 2 = true := by decide +kernel
theorem s170_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 3 = true := by decide +kernel
theorem s170_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 4 = true := by decide +kernel
theorem s170_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 5 = true := by decide +kernel
theorem k170_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k170_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k170_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k170_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k170_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k170_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s170_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k170_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k170_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k170_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k170_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k170_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 170) ((InDA2.TCasaD 5 5 6).getD (170 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k170_5_6_50 k h.1 (by omega)
theorem s170_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 5 7 = true := by decide +kernel
theorem col170_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 6 v) = true := by decide +kernel
theorem col170_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 7 v) = true := by decide +kernel
theorem col170 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 170) 170 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col170_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col170_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s170_2_0
    · exact s170_2_1
    · exact s170_2_2
    · exact s170_2_3
    · exact s170_2_4
    · exact s170_2_5
    · exact s170_2_6
    · exact s170_2_7
  · fin_cases v
    · exact s170_3_0
    · exact s170_3_1
    · exact s170_3_2
    · exact s170_3_3
    · exact s170_3_4
    · exact s170_3_5
    · exact s170_3_6
    · exact s170_3_7
  · fin_cases v
    · exact s170_4_0
    · exact s170_4_1
    · exact s170_4_2
    · exact s170_4_3
    · exact s170_4_4
    · exact s170_4_5
    · exact s170_4_6
    · exact s170_4_7
  · fin_cases v
    · exact s170_5_0
    · exact s170_5_1
    · exact s170_5_2
    · exact s170_5_3
    · exact s170_5_4
    · exact s170_5_5
    · exact s170_5_6
    · exact s170_5_7
  · exact List.all_eq_true.mp col170_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col170_7 v (List.mem_finRange v)
theorem col171_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 0 v) = true := by decide +kernel
theorem col171_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 1 v) = true := by decide +kernel
theorem s171_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 0 = true := by decide +kernel
theorem s171_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 1 = true := by decide +kernel
theorem s171_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 2 = true := by decide +kernel
theorem s171_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 3 = true := by decide +kernel
theorem k171_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k171_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k171_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s171_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k171_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k171_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k171_2_4_80 k h.1 (by omega)
theorem s171_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 5 = true := by decide +kernel
theorem s171_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 6 = true := by decide +kernel
theorem s171_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 2 7 = true := by decide +kernel
theorem s171_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 0 = true := by decide +kernel
theorem s171_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 1 = true := by decide +kernel
theorem s171_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 2 = true := by decide +kernel
theorem s171_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 3 = true := by decide +kernel
theorem k171_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k171_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k171_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s171_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k171_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k171_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k171_3_4_80 k h.1 (by omega)
theorem s171_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 5 = true := by decide +kernel
theorem s171_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 6 = true := by decide +kernel
theorem s171_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 3 7 = true := by decide +kernel
theorem s171_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 0 = true := by decide +kernel
theorem s171_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 1 = true := by decide +kernel
theorem s171_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 2 = true := by decide +kernel
theorem s171_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 3 = true := by decide +kernel
theorem k171_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k171_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k171_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k171_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k171_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k171_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k171_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k171_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k171_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k171_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k171_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k171_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k171_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k171_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k171_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k171_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k171_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k171_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k171_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k171_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k171_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s171_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k171_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k171_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k171_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k171_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k171_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k171_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k171_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k171_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k171_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k171_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k171_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k171_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k171_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k171_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k171_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k171_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k171_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k171_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k171_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k171_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k171_4_4_100 k h.1 (by omega)
theorem k171_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k171_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k171_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k171_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k171_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k171_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k171_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k171_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k171_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s171_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k171_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k171_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k171_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k171_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k171_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k171_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k171_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k171_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 171) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (171 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k171_4_5_40 k h.1 (by omega)
theorem k171_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k171_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k171_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k171_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k171_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k171_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k171_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k171_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k171_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k171_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k171_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s171_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k171_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k171_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k171_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k171_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k171_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k171_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k171_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k171_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k171_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k171_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TTsaaD 4 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k171_4_6_50 k h.1 (by omega)
theorem s171_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 4 7 = true := by decide +kernel
theorem s171_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 0 = true := by decide +kernel
theorem s171_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 1 = true := by decide +kernel
theorem s171_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 2 = true := by decide +kernel
theorem s171_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 3 = true := by decide +kernel
theorem s171_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 4 = true := by decide +kernel
theorem s171_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 5 = true := by decide +kernel
theorem k171_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k171_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k171_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k171_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k171_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k171_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s171_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k171_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k171_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k171_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k171_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k171_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 171) ((InDA2.TCasaD 5 5 6).getD (171 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k171_5_6_50 k h.1 (by omega)
theorem s171_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 5 7 = true := by decide +kernel
theorem col171_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 6 v) = true := by decide +kernel
theorem col171_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 7 v) = true := by decide +kernel
theorem col171 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 171) 171 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col171_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col171_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s171_2_0
    · exact s171_2_1
    · exact s171_2_2
    · exact s171_2_3
    · exact s171_2_4
    · exact s171_2_5
    · exact s171_2_6
    · exact s171_2_7
  · fin_cases v
    · exact s171_3_0
    · exact s171_3_1
    · exact s171_3_2
    · exact s171_3_3
    · exact s171_3_4
    · exact s171_3_5
    · exact s171_3_6
    · exact s171_3_7
  · fin_cases v
    · exact s171_4_0
    · exact s171_4_1
    · exact s171_4_2
    · exact s171_4_3
    · exact s171_4_4
    · exact s171_4_5
    · exact s171_4_6
    · exact s171_4_7
  · fin_cases v
    · exact s171_5_0
    · exact s171_5_1
    · exact s171_5_2
    · exact s171_5_3
    · exact s171_5_4
    · exact s171_5_5
    · exact s171_5_6
    · exact s171_5_7
  · exact List.all_eq_true.mp col171_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col171_7 v (List.mem_finRange v)
theorem col172_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 0 v) = true := by decide +kernel
theorem col172_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 1 v) = true := by decide +kernel
theorem s172_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 0 = true := by decide +kernel
theorem s172_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 1 = true := by decide +kernel
theorem s172_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 2 = true := by decide +kernel
theorem s172_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 3 = true := by decide +kernel
theorem k172_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k172_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k172_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s172_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k172_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k172_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k172_2_4_80 k h.1 (by omega)
theorem s172_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 5 = true := by decide +kernel
theorem s172_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 6 = true := by decide +kernel
theorem s172_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 2 7 = true := by decide +kernel
theorem s172_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 0 = true := by decide +kernel
theorem s172_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 1 = true := by decide +kernel
theorem s172_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 2 = true := by decide +kernel
theorem s172_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 3 = true := by decide +kernel
theorem k172_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k172_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k172_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s172_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k172_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k172_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k172_3_4_80 k h.1 (by omega)
theorem s172_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 5 = true := by decide +kernel
theorem s172_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 6 = true := by decide +kernel
theorem s172_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 3 7 = true := by decide +kernel
theorem s172_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 0 = true := by decide +kernel
theorem s172_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 1 = true := by decide +kernel
theorem s172_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 2 = true := by decide +kernel
theorem s172_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 3 = true := by decide +kernel
theorem k172_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k172_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k172_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k172_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k172_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k172_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k172_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k172_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k172_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k172_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k172_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k172_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k172_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k172_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k172_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k172_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k172_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k172_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k172_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k172_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k172_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s172_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k172_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k172_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k172_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k172_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k172_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k172_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k172_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k172_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k172_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k172_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k172_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k172_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k172_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k172_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k172_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k172_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k172_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k172_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k172_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k172_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k172_4_4_100 k h.1 (by omega)
theorem k172_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k172_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k172_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k172_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k172_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k172_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k172_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k172_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k172_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s172_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k172_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k172_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k172_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k172_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k172_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k172_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k172_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k172_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 172) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (172 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k172_4_5_40 k h.1 (by omega)
theorem k172_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k172_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k172_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k172_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k172_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k172_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k172_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k172_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k172_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k172_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k172_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s172_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k172_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k172_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k172_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k172_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k172_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k172_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k172_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k172_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k172_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k172_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TTsaaD 4 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k172_4_6_50 k h.1 (by omega)
theorem s172_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 4 7 = true := by decide +kernel
theorem s172_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 0 = true := by decide +kernel
theorem s172_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 1 = true := by decide +kernel
theorem s172_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 2 = true := by decide +kernel
theorem s172_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 3 = true := by decide +kernel
theorem s172_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 4 = true := by decide +kernel
theorem s172_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 5 = true := by decide +kernel
theorem k172_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k172_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k172_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k172_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k172_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k172_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s172_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k172_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k172_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k172_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k172_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k172_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 172) ((InDA2.TCasaD 5 5 6).getD (172 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k172_5_6_50 k h.1 (by omega)
theorem s172_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 5 7 = true := by decide +kernel
theorem col172_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 6 v) = true := by decide +kernel
theorem col172_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 7 v) = true := by decide +kernel
theorem col172 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 172) 172 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col172_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col172_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s172_2_0
    · exact s172_2_1
    · exact s172_2_2
    · exact s172_2_3
    · exact s172_2_4
    · exact s172_2_5
    · exact s172_2_6
    · exact s172_2_7
  · fin_cases v
    · exact s172_3_0
    · exact s172_3_1
    · exact s172_3_2
    · exact s172_3_3
    · exact s172_3_4
    · exact s172_3_5
    · exact s172_3_6
    · exact s172_3_7
  · fin_cases v
    · exact s172_4_0
    · exact s172_4_1
    · exact s172_4_2
    · exact s172_4_3
    · exact s172_4_4
    · exact s172_4_5
    · exact s172_4_6
    · exact s172_4_7
  · fin_cases v
    · exact s172_5_0
    · exact s172_5_1
    · exact s172_5_2
    · exact s172_5_3
    · exact s172_5_4
    · exact s172_5_5
    · exact s172_5_6
    · exact s172_5_7
  · exact List.all_eq_true.mp col172_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col172_7 v (List.mem_finRange v)
theorem col173_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 0 v) = true := by decide +kernel
theorem col173_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 1 v) = true := by decide +kernel
theorem s173_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 0 = true := by decide +kernel
theorem s173_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 1 = true := by decide +kernel
theorem s173_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 2 = true := by decide +kernel
theorem s173_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 3 = true := by decide +kernel
theorem k173_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k173_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k173_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s173_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k173_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k173_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k173_2_4_80 k h.1 (by omega)
theorem s173_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 5 = true := by decide +kernel
theorem s173_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 6 = true := by decide +kernel
theorem s173_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 2 7 = true := by decide +kernel
theorem s173_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 0 = true := by decide +kernel
theorem s173_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 1 = true := by decide +kernel
theorem s173_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 2 = true := by decide +kernel
theorem s173_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 3 = true := by decide +kernel
theorem k173_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k173_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k173_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s173_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k173_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k173_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k173_3_4_80 k h.1 (by omega)
theorem s173_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 5 = true := by decide +kernel
theorem s173_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 6 = true := by decide +kernel
theorem s173_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 3 7 = true := by decide +kernel
theorem s173_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 0 = true := by decide +kernel
theorem s173_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 1 = true := by decide +kernel
theorem s173_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 2 = true := by decide +kernel
theorem s173_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 3 = true := by decide +kernel
theorem k173_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k173_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k173_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k173_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k173_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k173_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k173_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k173_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k173_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k173_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k173_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k173_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k173_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k173_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k173_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k173_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k173_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k173_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k173_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k173_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k173_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s173_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k173_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k173_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k173_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k173_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k173_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k173_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k173_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k173_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k173_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k173_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k173_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k173_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k173_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k173_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k173_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k173_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k173_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k173_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k173_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k173_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k173_4_4_100 k h.1 (by omega)
theorem k173_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k173_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k173_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k173_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k173_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k173_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k173_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k173_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k173_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s173_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k173_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k173_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k173_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k173_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k173_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k173_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k173_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k173_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 173) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (173 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k173_4_5_40 k h.1 (by omega)
theorem k173_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k173_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k173_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k173_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k173_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k173_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k173_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k173_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k173_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k173_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k173_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s173_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k173_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k173_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k173_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k173_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k173_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k173_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k173_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k173_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k173_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k173_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TTsaaD 4 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k173_4_6_50 k h.1 (by omega)
theorem s173_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 4 7 = true := by decide +kernel
theorem s173_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 0 = true := by decide +kernel
theorem s173_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 1 = true := by decide +kernel
theorem s173_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 2 = true := by decide +kernel
theorem s173_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 3 = true := by decide +kernel
theorem s173_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 4 = true := by decide +kernel
theorem s173_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 5 = true := by decide +kernel
theorem k173_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k173_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k173_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k173_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k173_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k173_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s173_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k173_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k173_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k173_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k173_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k173_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 173) ((InDA2.TCasaD 5 5 6).getD (173 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k173_5_6_50 k h.1 (by omega)
theorem s173_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 5 7 = true := by decide +kernel
theorem col173_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 6 v) = true := by decide +kernel
theorem col173_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 7 v) = true := by decide +kernel
theorem col173 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 173) 173 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col173_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col173_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s173_2_0
    · exact s173_2_1
    · exact s173_2_2
    · exact s173_2_3
    · exact s173_2_4
    · exact s173_2_5
    · exact s173_2_6
    · exact s173_2_7
  · fin_cases v
    · exact s173_3_0
    · exact s173_3_1
    · exact s173_3_2
    · exact s173_3_3
    · exact s173_3_4
    · exact s173_3_5
    · exact s173_3_6
    · exact s173_3_7
  · fin_cases v
    · exact s173_4_0
    · exact s173_4_1
    · exact s173_4_2
    · exact s173_4_3
    · exact s173_4_4
    · exact s173_4_5
    · exact s173_4_6
    · exact s173_4_7
  · fin_cases v
    · exact s173_5_0
    · exact s173_5_1
    · exact s173_5_2
    · exact s173_5_3
    · exact s173_5_4
    · exact s173_5_5
    · exact s173_5_6
    · exact s173_5_7
  · exact List.all_eq_true.mp col173_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col173_7 v (List.mem_finRange v)
theorem col174_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 0 v) = true := by decide +kernel
theorem col174_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 1 v) = true := by decide +kernel
theorem s174_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 0 = true := by decide +kernel
theorem s174_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 1 = true := by decide +kernel
theorem s174_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 2 = true := by decide +kernel
theorem s174_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 3 = true := by decide +kernel
theorem k174_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k174_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k174_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s174_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k174_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k174_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 2 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k174_2_4_80 k h.1 (by omega)
theorem s174_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 5 = true := by decide +kernel
theorem s174_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 6 = true := by decide +kernel
theorem s174_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 2 7 = true := by decide +kernel
theorem s174_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 0 = true := by decide +kernel
theorem s174_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 1 = true := by decide +kernel
theorem s174_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 2 = true := by decide +kernel
theorem s174_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 3 = true := by decide +kernel
theorem k174_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k174_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k174_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s174_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k174_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k174_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 3 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k174_3_4_80 k h.1 (by omega)
theorem s174_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 5 = true := by decide +kernel
theorem s174_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 6 = true := by decide +kernel
theorem s174_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 3 7 = true := by decide +kernel
theorem s174_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 0 = true := by decide +kernel
theorem s174_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 1 = true := by decide +kernel
theorem s174_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 2 = true := by decide +kernel
theorem s174_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 3 = true := by decide +kernel
theorem k174_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k174_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k174_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k174_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k174_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k174_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k174_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k174_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k174_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k174_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k174_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k174_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k174_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k174_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k174_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k174_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k174_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k174_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k174_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k174_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k174_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s174_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k174_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k174_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k174_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k174_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k174_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k174_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k174_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k174_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k174_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k174_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k174_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k174_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k174_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k174_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k174_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k174_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k174_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k174_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k174_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k174_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TCasaD 4 4 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k174_4_4_100 k h.1 (by omega)
theorem k174_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k174_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k174_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k174_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k174_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k174_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k174_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k174_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k174_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s174_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 5 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k174_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k174_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k174_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k174_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k174_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k174_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k174_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k174_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 174) (InDA2.TTsaaD 4 5 5) (posA (x2Mult 2 5) (174 - x2AOff 2 5)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k174_4_5_40 k h.1 (by omega)
theorem k174_4_6_0 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k174_4_6_5 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k174_4_6_10 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k174_4_6_15 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k174_4_6_20 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k174_4_6_25 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k174_4_6_30 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k174_4_6_35 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k174_4_6_40 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k174_4_6_45 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k174_4_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s174_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 6 = true := by
  rw [segOKA_gPT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k174_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k174_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k174_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k174_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k174_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k174_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k174_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k174_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k174_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k174_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TTsaaD 4 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k174_4_6_50 k h.1 (by omega)
theorem s174_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 4 7 = true := by decide +kernel
theorem s174_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 0 = true := by decide +kernel
theorem s174_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 1 = true := by decide +kernel
theorem s174_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 2 = true := by decide +kernel
theorem s174_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 3 = true := by decide +kernel
theorem s174_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 4 = true := by decide +kernel
theorem s174_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 5 = true := by decide +kernel
theorem k174_5_6_0 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k174_5_6_10 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k174_5_6_20 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k174_5_6_30 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k174_5_6_40 : (List.range 10).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k174_5_6_50 : (List.range 5).all (fun k => (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s174_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 6 = true := by
  rw [segOKA_gPC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherPosOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k174_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k174_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k174_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k174_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k174_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gPrun (colFibers CoreA2g.f0 174) ((InDA2.TCasaD 5 5 6).getD (174 - x2AOff 2 5) []) (posA (x2Mult 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k174_5_6_50 k h.1 (by omega)
theorem s174_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 5 7 = true := by decide +kernel
theorem col174_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 6 v) = true := by decide +kernel
theorem col174_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 7 v) = true := by decide +kernel
theorem col174 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 174) 174 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col174_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col174_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s174_2_0
    · exact s174_2_1
    · exact s174_2_2
    · exact s174_2_3
    · exact s174_2_4
    · exact s174_2_5
    · exact s174_2_6
    · exact s174_2_7
  · fin_cases v
    · exact s174_3_0
    · exact s174_3_1
    · exact s174_3_2
    · exact s174_3_3
    · exact s174_3_4
    · exact s174_3_5
    · exact s174_3_6
    · exact s174_3_7
  · fin_cases v
    · exact s174_4_0
    · exact s174_4_1
    · exact s174_4_2
    · exact s174_4_3
    · exact s174_4_4
    · exact s174_4_5
    · exact s174_4_6
    · exact s174_4_7
  · fin_cases v
    · exact s174_5_0
    · exact s174_5_1
    · exact s174_5_2
    · exact s174_5_3
    · exact s174_5_4
    · exact s174_5_5
    · exact s174_5_6
    · exact s174_5_7
  · exact List.all_eq_true.mp col174_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col174_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
