module

public import ThreeCopyQutritWerner.CertificateX2InputDA2
public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2InputSegA2

@[expose] public section


/-! Segment checks of the A2g input table, columns [190, 195). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col190_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 0 v) = true := by decide +kernel
theorem col190_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 1 v) = true := by decide +kernel
theorem s190_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 0 = true := by decide +kernel
theorem s190_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 1 = true := by decide +kernel
theorem s190_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 2 = true := by decide +kernel
theorem s190_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 3 = true := by decide +kernel
theorem k190_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k190_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k190_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s190_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k190_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k190_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k190_2_4_80 k h.1 (by omega)
theorem s190_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 5 = true := by decide +kernel
theorem s190_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 6 = true := by decide +kernel
theorem s190_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 2 7 = true := by decide +kernel
theorem s190_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 0 = true := by decide +kernel
theorem s190_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 1 = true := by decide +kernel
theorem s190_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 2 = true := by decide +kernel
theorem s190_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 3 = true := by decide +kernel
theorem k190_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k190_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k190_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s190_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k190_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k190_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k190_3_4_80 k h.1 (by omega)
theorem s190_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 5 = true := by decide +kernel
theorem s190_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 6 = true := by decide +kernel
theorem s190_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 3 7 = true := by decide +kernel
theorem s190_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 0 = true := by decide +kernel
theorem s190_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 1 = true := by decide +kernel
theorem s190_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 2 = true := by decide +kernel
theorem s190_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 3 = true := by decide +kernel
theorem k190_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k190_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k190_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k190_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k190_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k190_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k190_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k190_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k190_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k190_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k190_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k190_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k190_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k190_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k190_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k190_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k190_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k190_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k190_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k190_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k190_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s190_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k190_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k190_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k190_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k190_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k190_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k190_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k190_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k190_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k190_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k190_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k190_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k190_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k190_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k190_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k190_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k190_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k190_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k190_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k190_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k190_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k190_4_4_100 k h.1 (by omega)
theorem k190_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k190_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k190_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k190_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k190_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k190_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k190_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k190_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k190_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s190_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k190_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k190_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k190_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k190_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k190_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k190_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k190_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k190_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k190_4_5_40 k h.1 (by omega)
theorem k190_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k190_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k190_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k190_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k190_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k190_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k190_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k190_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k190_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k190_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k190_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s190_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k190_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k190_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k190_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k190_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k190_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k190_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k190_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k190_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k190_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k190_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k190_4_6_50 k h.1 (by omega)
theorem s190_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 4 7 = true := by decide +kernel
theorem s190_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 0 = true := by decide +kernel
theorem s190_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 1 = true := by decide +kernel
theorem s190_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 2 = true := by decide +kernel
theorem s190_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 3 = true := by decide +kernel
theorem k190_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k190_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k190_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k190_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k190_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k190_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k190_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k190_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k190_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k190_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k190_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s190_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k190_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k190_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k190_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k190_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k190_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k190_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k190_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k190_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k190_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k190_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k190_5_4_100 k h.1 (by omega)
theorem k190_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k190_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k190_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k190_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k190_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s190_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k190_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k190_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k190_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k190_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k190_5_5_40 k h.1 (by omega)
theorem k190_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k190_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k190_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k190_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k190_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k190_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s190_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k190_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k190_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k190_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k190_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k190_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 190) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (190 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k190_5_6_50 k h.1 (by omega)
theorem s190_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 5 7 = true := by decide +kernel
theorem col190_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 6 v) = true := by decide +kernel
theorem col190_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 7 v) = true := by decide +kernel
theorem col190 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 190) 190 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col190_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col190_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s190_2_0
    · exact s190_2_1
    · exact s190_2_2
    · exact s190_2_3
    · exact s190_2_4
    · exact s190_2_5
    · exact s190_2_6
    · exact s190_2_7
  · fin_cases v
    · exact s190_3_0
    · exact s190_3_1
    · exact s190_3_2
    · exact s190_3_3
    · exact s190_3_4
    · exact s190_3_5
    · exact s190_3_6
    · exact s190_3_7
  · fin_cases v
    · exact s190_4_0
    · exact s190_4_1
    · exact s190_4_2
    · exact s190_4_3
    · exact s190_4_4
    · exact s190_4_5
    · exact s190_4_6
    · exact s190_4_7
  · fin_cases v
    · exact s190_5_0
    · exact s190_5_1
    · exact s190_5_2
    · exact s190_5_3
    · exact s190_5_4
    · exact s190_5_5
    · exact s190_5_6
    · exact s190_5_7
  · exact List.all_eq_true.mp col190_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col190_7 v (List.mem_finRange v)
theorem col191_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 0 v) = true := by decide +kernel
theorem col191_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 1 v) = true := by decide +kernel
theorem s191_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 0 = true := by decide +kernel
theorem s191_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 1 = true := by decide +kernel
theorem s191_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 2 = true := by decide +kernel
theorem s191_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 3 = true := by decide +kernel
theorem k191_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k191_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k191_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s191_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k191_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k191_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k191_2_4_80 k h.1 (by omega)
theorem s191_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 5 = true := by decide +kernel
theorem s191_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 6 = true := by decide +kernel
theorem s191_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 2 7 = true := by decide +kernel
theorem s191_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 0 = true := by decide +kernel
theorem s191_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 1 = true := by decide +kernel
theorem s191_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 2 = true := by decide +kernel
theorem s191_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 3 = true := by decide +kernel
theorem k191_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k191_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k191_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s191_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k191_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k191_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k191_3_4_80 k h.1 (by omega)
theorem s191_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 5 = true := by decide +kernel
theorem s191_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 6 = true := by decide +kernel
theorem s191_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 3 7 = true := by decide +kernel
theorem s191_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 0 = true := by decide +kernel
theorem s191_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 1 = true := by decide +kernel
theorem s191_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 2 = true := by decide +kernel
theorem s191_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 3 = true := by decide +kernel
theorem k191_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k191_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k191_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k191_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k191_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k191_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k191_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k191_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k191_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k191_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k191_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k191_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k191_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k191_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k191_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k191_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k191_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k191_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k191_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k191_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k191_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s191_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k191_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k191_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k191_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k191_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k191_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k191_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k191_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k191_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k191_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k191_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k191_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k191_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k191_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k191_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k191_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k191_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k191_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k191_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k191_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k191_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k191_4_4_100 k h.1 (by omega)
theorem k191_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k191_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k191_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k191_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k191_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k191_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k191_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k191_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k191_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s191_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k191_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k191_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k191_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k191_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k191_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k191_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k191_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k191_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k191_4_5_40 k h.1 (by omega)
theorem k191_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k191_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k191_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k191_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k191_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k191_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k191_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k191_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k191_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k191_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k191_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s191_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k191_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k191_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k191_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k191_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k191_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k191_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k191_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k191_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k191_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k191_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k191_4_6_50 k h.1 (by omega)
theorem s191_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 4 7 = true := by decide +kernel
theorem s191_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 0 = true := by decide +kernel
theorem s191_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 1 = true := by decide +kernel
theorem s191_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 2 = true := by decide +kernel
theorem s191_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 3 = true := by decide +kernel
theorem k191_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k191_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k191_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k191_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k191_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k191_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k191_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k191_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k191_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k191_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k191_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s191_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k191_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k191_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k191_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k191_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k191_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k191_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k191_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k191_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k191_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k191_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k191_5_4_100 k h.1 (by omega)
theorem k191_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k191_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k191_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k191_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k191_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s191_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k191_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k191_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k191_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k191_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k191_5_5_40 k h.1 (by omega)
theorem k191_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k191_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k191_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k191_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k191_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k191_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s191_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k191_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k191_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k191_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k191_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k191_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 191) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (191 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k191_5_6_50 k h.1 (by omega)
theorem s191_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 5 7 = true := by decide +kernel
theorem col191_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 6 v) = true := by decide +kernel
theorem col191_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 7 v) = true := by decide +kernel
theorem col191 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 191) 191 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col191_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col191_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s191_2_0
    · exact s191_2_1
    · exact s191_2_2
    · exact s191_2_3
    · exact s191_2_4
    · exact s191_2_5
    · exact s191_2_6
    · exact s191_2_7
  · fin_cases v
    · exact s191_3_0
    · exact s191_3_1
    · exact s191_3_2
    · exact s191_3_3
    · exact s191_3_4
    · exact s191_3_5
    · exact s191_3_6
    · exact s191_3_7
  · fin_cases v
    · exact s191_4_0
    · exact s191_4_1
    · exact s191_4_2
    · exact s191_4_3
    · exact s191_4_4
    · exact s191_4_5
    · exact s191_4_6
    · exact s191_4_7
  · fin_cases v
    · exact s191_5_0
    · exact s191_5_1
    · exact s191_5_2
    · exact s191_5_3
    · exact s191_5_4
    · exact s191_5_5
    · exact s191_5_6
    · exact s191_5_7
  · exact List.all_eq_true.mp col191_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col191_7 v (List.mem_finRange v)
theorem col192_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 0 v) = true := by decide +kernel
theorem col192_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 1 v) = true := by decide +kernel
theorem s192_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 0 = true := by decide +kernel
theorem s192_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 1 = true := by decide +kernel
theorem s192_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 2 = true := by decide +kernel
theorem s192_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 3 = true := by decide +kernel
theorem k192_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k192_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k192_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s192_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k192_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k192_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k192_2_4_80 k h.1 (by omega)
theorem s192_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 5 = true := by decide +kernel
theorem s192_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 6 = true := by decide +kernel
theorem s192_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 2 7 = true := by decide +kernel
theorem s192_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 0 = true := by decide +kernel
theorem s192_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 1 = true := by decide +kernel
theorem s192_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 2 = true := by decide +kernel
theorem s192_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 3 = true := by decide +kernel
theorem k192_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k192_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k192_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s192_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k192_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k192_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k192_3_4_80 k h.1 (by omega)
theorem s192_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 5 = true := by decide +kernel
theorem s192_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 6 = true := by decide +kernel
theorem s192_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 3 7 = true := by decide +kernel
theorem s192_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 0 = true := by decide +kernel
theorem s192_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 1 = true := by decide +kernel
theorem s192_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 2 = true := by decide +kernel
theorem s192_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 3 = true := by decide +kernel
theorem k192_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k192_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k192_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k192_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k192_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k192_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k192_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k192_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k192_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k192_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k192_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k192_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k192_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k192_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k192_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k192_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k192_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k192_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k192_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k192_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k192_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s192_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k192_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k192_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k192_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k192_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k192_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k192_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k192_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k192_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k192_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k192_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k192_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k192_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k192_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k192_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k192_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k192_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k192_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k192_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k192_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k192_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k192_4_4_100 k h.1 (by omega)
theorem k192_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k192_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k192_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k192_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k192_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k192_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k192_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k192_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k192_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s192_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k192_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k192_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k192_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k192_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k192_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k192_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k192_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k192_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k192_4_5_40 k h.1 (by omega)
theorem k192_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k192_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k192_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k192_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k192_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k192_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k192_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k192_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k192_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k192_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k192_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s192_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k192_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k192_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k192_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k192_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k192_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k192_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k192_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k192_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k192_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k192_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k192_4_6_50 k h.1 (by omega)
theorem s192_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 4 7 = true := by decide +kernel
theorem s192_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 0 = true := by decide +kernel
theorem s192_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 1 = true := by decide +kernel
theorem s192_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 2 = true := by decide +kernel
theorem s192_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 3 = true := by decide +kernel
theorem k192_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k192_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k192_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k192_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k192_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k192_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k192_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k192_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k192_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k192_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k192_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s192_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k192_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k192_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k192_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k192_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k192_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k192_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k192_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k192_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k192_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k192_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k192_5_4_100 k h.1 (by omega)
theorem k192_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k192_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k192_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k192_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k192_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s192_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k192_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k192_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k192_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k192_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k192_5_5_40 k h.1 (by omega)
theorem k192_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k192_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k192_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k192_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k192_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k192_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s192_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k192_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k192_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k192_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k192_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k192_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 192) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (192 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k192_5_6_50 k h.1 (by omega)
theorem s192_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 5 7 = true := by decide +kernel
theorem col192_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 6 v) = true := by decide +kernel
theorem col192_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 7 v) = true := by decide +kernel
theorem col192 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 192) 192 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col192_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col192_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s192_2_0
    · exact s192_2_1
    · exact s192_2_2
    · exact s192_2_3
    · exact s192_2_4
    · exact s192_2_5
    · exact s192_2_6
    · exact s192_2_7
  · fin_cases v
    · exact s192_3_0
    · exact s192_3_1
    · exact s192_3_2
    · exact s192_3_3
    · exact s192_3_4
    · exact s192_3_5
    · exact s192_3_6
    · exact s192_3_7
  · fin_cases v
    · exact s192_4_0
    · exact s192_4_1
    · exact s192_4_2
    · exact s192_4_3
    · exact s192_4_4
    · exact s192_4_5
    · exact s192_4_6
    · exact s192_4_7
  · fin_cases v
    · exact s192_5_0
    · exact s192_5_1
    · exact s192_5_2
    · exact s192_5_3
    · exact s192_5_4
    · exact s192_5_5
    · exact s192_5_6
    · exact s192_5_7
  · exact List.all_eq_true.mp col192_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col192_7 v (List.mem_finRange v)
theorem col193_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 0 v) = true := by decide +kernel
theorem col193_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 1 v) = true := by decide +kernel
theorem s193_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 0 = true := by decide +kernel
theorem s193_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 1 = true := by decide +kernel
theorem s193_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 2 = true := by decide +kernel
theorem s193_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 3 = true := by decide +kernel
theorem k193_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k193_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k193_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s193_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k193_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k193_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k193_2_4_80 k h.1 (by omega)
theorem s193_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 5 = true := by decide +kernel
theorem s193_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 6 = true := by decide +kernel
theorem s193_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 2 7 = true := by decide +kernel
theorem s193_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 0 = true := by decide +kernel
theorem s193_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 1 = true := by decide +kernel
theorem s193_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 2 = true := by decide +kernel
theorem s193_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 3 = true := by decide +kernel
theorem k193_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k193_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k193_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s193_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k193_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k193_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k193_3_4_80 k h.1 (by omega)
theorem s193_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 5 = true := by decide +kernel
theorem s193_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 6 = true := by decide +kernel
theorem s193_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 3 7 = true := by decide +kernel
theorem s193_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 0 = true := by decide +kernel
theorem s193_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 1 = true := by decide +kernel
theorem s193_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 2 = true := by decide +kernel
theorem s193_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 3 = true := by decide +kernel
theorem k193_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k193_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k193_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k193_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k193_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k193_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k193_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k193_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k193_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k193_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k193_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k193_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k193_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k193_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k193_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k193_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k193_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k193_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k193_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k193_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k193_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s193_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k193_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k193_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k193_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k193_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k193_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k193_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k193_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k193_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k193_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k193_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k193_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k193_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k193_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k193_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k193_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k193_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k193_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k193_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k193_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k193_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k193_4_4_100 k h.1 (by omega)
theorem k193_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k193_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k193_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k193_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k193_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k193_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k193_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k193_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k193_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s193_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k193_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k193_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k193_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k193_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k193_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k193_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k193_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k193_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k193_4_5_40 k h.1 (by omega)
theorem k193_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k193_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k193_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k193_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k193_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k193_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k193_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k193_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k193_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k193_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k193_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s193_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k193_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k193_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k193_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k193_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k193_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k193_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k193_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k193_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k193_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k193_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k193_4_6_50 k h.1 (by omega)
theorem s193_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 4 7 = true := by decide +kernel
theorem s193_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 0 = true := by decide +kernel
theorem s193_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 1 = true := by decide +kernel
theorem s193_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 2 = true := by decide +kernel
theorem s193_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 3 = true := by decide +kernel
theorem k193_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k193_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k193_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k193_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k193_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k193_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k193_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k193_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k193_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k193_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k193_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s193_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k193_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k193_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k193_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k193_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k193_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k193_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k193_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k193_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k193_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k193_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k193_5_4_100 k h.1 (by omega)
theorem k193_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k193_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k193_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k193_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k193_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s193_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k193_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k193_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k193_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k193_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k193_5_5_40 k h.1 (by omega)
theorem k193_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k193_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k193_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k193_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k193_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k193_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s193_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k193_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k193_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k193_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k193_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k193_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 193) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (193 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k193_5_6_50 k h.1 (by omega)
theorem s193_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 5 7 = true := by decide +kernel
theorem col193_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 6 v) = true := by decide +kernel
theorem col193_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 7 v) = true := by decide +kernel
theorem col193 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 193) 193 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col193_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col193_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s193_2_0
    · exact s193_2_1
    · exact s193_2_2
    · exact s193_2_3
    · exact s193_2_4
    · exact s193_2_5
    · exact s193_2_6
    · exact s193_2_7
  · fin_cases v
    · exact s193_3_0
    · exact s193_3_1
    · exact s193_3_2
    · exact s193_3_3
    · exact s193_3_4
    · exact s193_3_5
    · exact s193_3_6
    · exact s193_3_7
  · fin_cases v
    · exact s193_4_0
    · exact s193_4_1
    · exact s193_4_2
    · exact s193_4_3
    · exact s193_4_4
    · exact s193_4_5
    · exact s193_4_6
    · exact s193_4_7
  · fin_cases v
    · exact s193_5_0
    · exact s193_5_1
    · exact s193_5_2
    · exact s193_5_3
    · exact s193_5_4
    · exact s193_5_5
    · exact s193_5_6
    · exact s193_5_7
  · exact List.all_eq_true.mp col193_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col193_7 v (List.mem_finRange v)
theorem col194_0 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 0 v) = true := by decide +kernel
theorem col194_1 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 1 v) = true := by decide +kernel
theorem s194_2_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 0 = true := by decide +kernel
theorem s194_2_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 1 = true := by decide +kernel
theorem s194_2_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 2 = true := by decide +kernel
theorem s194_2_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 3 = true := by decide +kernel
theorem k194_2_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (0 + k)) = true := by decide +kernel
theorem k194_2_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (40 + k)) = true := by decide +kernel
theorem k194_2_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) (80 + k)) = true := by decide +kernel
theorem s194_2_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 0 40 k194_2_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 40 40 k194_2_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 2 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 2) (nS 2 2)) 80 25 k194_2_4_80 k h.1 (by omega)
theorem s194_2_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 5 = true := by decide +kernel
theorem s194_2_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 6 = true := by decide +kernel
theorem s194_2_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 2 7 = true := by decide +kernel
theorem s194_3_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 0 = true := by decide +kernel
theorem s194_3_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 1 = true := by decide +kernel
theorem s194_3_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 2 = true := by decide +kernel
theorem s194_3_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 3 = true := by decide +kernel
theorem k194_3_4_0 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (0 + k)) = true := by decide +kernel
theorem k194_3_4_40 : (List.range 40).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (40 + k)) = true := by decide +kernel
theorem k194_3_4_80 : (List.range 25).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) (80 + k)) = true := by decide +kernel
theorem s194_3_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 4 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 105)) with h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 0 40 k194_3_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 40 40 k194_3_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 3 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 3) (nS 2 3)) 80 25 k194_3_4_80 k h.1 (by omega)
theorem s194_3_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 5 = true := by decide +kernel
theorem s194_3_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 6 = true := by decide +kernel
theorem s194_3_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 3 7 = true := by decide +kernel
theorem s194_4_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 0 = true := by decide +kernel
theorem s194_4_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 1 = true := by decide +kernel
theorem s194_4_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 2 = true := by decide +kernel
theorem s194_4_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 3 = true := by decide +kernel
theorem k194_4_4_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k194_4_4_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k194_4_4_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k194_4_4_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k194_4_4_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k194_4_4_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k194_4_4_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k194_4_4_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k194_4_4_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k194_4_4_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k194_4_4_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem k194_4_4_55 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (55 + k)) = true := by decide +kernel
theorem k194_4_4_60 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (60 + k)) = true := by decide +kernel
theorem k194_4_4_65 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (65 + k)) = true := by decide +kernel
theorem k194_4_4_70 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (70 + k)) = true := by decide +kernel
theorem k194_4_4_75 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (75 + k)) = true := by decide +kernel
theorem k194_4_4_80 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (80 + k)) = true := by decide +kernel
theorem k194_4_4_85 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (85 + k)) = true := by decide +kernel
theorem k194_4_4_90 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (90 + k)) = true := by decide +kernel
theorem k194_4_4_95 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (95 + k)) = true := by decide +kernel
theorem k194_4_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) (100 + k)) = true := by decide +kernel
theorem s194_4_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55) ∨ (55 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 65) ∨ (65 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 75) ∨ (75 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 85) ∨ (85 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 95) ∨ (95 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 0 5 k194_4_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 5 5 k194_4_4_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 10 5 k194_4_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 15 5 k194_4_4_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 20 5 k194_4_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 25 5 k194_4_4_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 30 5 k194_4_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 35 5 k194_4_4_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 40 5 k194_4_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 45 5 k194_4_4_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 50 5 k194_4_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 55 5 k194_4_4_55 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 60 5 k194_4_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 65 5 k194_4_4_65 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 70 5 k194_4_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 75 5 k194_4_4_75 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 80 5 k194_4_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 85 5 k194_4_4_85 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 90 5 k194_4_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 95 5 k194_4_4_95 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 4 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 4) (nS 2 4)) 100 5 k194_4_4_100 k h.1 (by omega)
theorem k194_4_5_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k194_4_5_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k194_4_5_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k194_4_5_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k194_4_5_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k194_4_5_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k194_4_5_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k194_4_5_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k194_4_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem s194_4_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 5 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 0 5 k194_4_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 5 5 k194_4_5_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 10 5 k194_4_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 15 5 k194_4_5_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 20 5 k194_4_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 25 5 k194_4_5_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 30 5 k194_4_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 35 5 k194_4_5_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 4) (nS 2 4)) 40 5 k194_4_5_40 k h.1 (by omega)
theorem k194_4_6_0 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (0 + k)) = true := by decide +kernel
theorem k194_4_6_5 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (5 + k)) = true := by decide +kernel
theorem k194_4_6_10 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (10 + k)) = true := by decide +kernel
theorem k194_4_6_15 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (15 + k)) = true := by decide +kernel
theorem k194_4_6_20 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (20 + k)) = true := by decide +kernel
theorem k194_4_6_25 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (25 + k)) = true := by decide +kernel
theorem k194_4_6_30 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (30 + k)) = true := by decide +kernel
theorem k194_4_6_35 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (35 + k)) = true := by decide +kernel
theorem k194_4_6_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (40 + k)) = true := by decide +kernel
theorem k194_4_6_45 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (45 + k)) = true := by decide +kernel
theorem k194_4_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) (50 + k)) = true := by decide +kernel
theorem s194_4_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 5) ∨ (5 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 15) ∨ (15 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 25) ∨ (25 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 35) ∨ (35 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45) ∨ (45 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 0 5 k194_4_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 5 5 k194_4_6_5 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 10 5 k194_4_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 15 5 k194_4_6_15 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 20 5 k194_4_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 25 5 k194_4_6_25 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 30 5 k194_4_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 35 5 k194_4_6_35 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 40 5 k194_4_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 45 5 k194_4_6_45 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 4 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 4) (nS 2 4)) 50 5 k194_4_6_50 k h.1 (by omega)
theorem s194_4_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 4 7 = true := by decide +kernel
theorem s194_5_0 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 0 = true := by decide +kernel
theorem s194_5_1 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 1 = true := by decide +kernel
theorem s194_5_2 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 2 = true := by decide +kernel
theorem s194_5_3 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 3 = true := by decide +kernel
theorem k194_5_4_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k194_5_4_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k194_5_4_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k194_5_4_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k194_5_4_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k194_5_4_50 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem k194_5_4_60 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (60 + k)) = true := by decide +kernel
theorem k194_5_4_70 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (70 + k)) = true := by decide +kernel
theorem k194_5_4_80 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (80 + k)) = true := by decide +kernel
theorem k194_5_4_90 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (90 + k)) = true := by decide +kernel
theorem k194_5_4_100 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) (100 + k)) = true := by decide +kernel
theorem s194_5_4 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 4 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 4 = 105 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ (70 ≤ k ∧ k < 80) ∨ (80 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 100) ∨ (100 ≤ k ∧ k < 105)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 0 10 k194_5_4_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 10 10 k194_5_4_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 20 10 k194_5_4_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 30 10 k194_5_4_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 40 10 k194_5_4_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 50 10 k194_5_4_50 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 60 10 k194_5_4_60 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 70 10 k194_5_4_70 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 80 10 k194_5_4_80 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 90 10 k194_5_4_90 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 4 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 4) (x2SOff 2 5) (nS 2 5)) 100 5 k194_5_4_100 k h.1 (by omega)
theorem k194_5_5_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k194_5_5_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k194_5_5_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k194_5_5_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k194_5_5_40 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem s194_5_5 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 5 = true := by
  rw [segOKA_gRC 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 5 = 45 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 45)) with h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 0 10 k194_5_5_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 10 10 k194_5_5_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 20 10 k194_5_5_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 30 10 k194_5_5_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TCasaD 5 5 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 5) (x2SOff 2 5) (nS 2 5)) 40 5 k194_5_5_40 k h.1 (by omega)
theorem k194_5_6_0 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (0 + k)) = true := by decide +kernel
theorem k194_5_6_10 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (10 + k)) = true := by decide +kernel
theorem k194_5_6_20 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (20 + k)) = true := by decide +kernel
theorem k194_5_6_30 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (30 + k)) = true := by decide +kernel
theorem k194_5_6_40 : (List.range 10).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (40 + k)) = true := by decide +kernel
theorem k194_5_6_50 : (List.range 5).all (fun k => (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) (50 + k)) = true := by decide +kernel
theorem s194_5_6 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 6 = true := by
  rw [segOKA_gRT 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine gatherRowsOKA_of _ _ _ _ _ _ _ (by decide +kernel) (fun k hk => ?_)
  have hn : nA 2 6 = 55 := by decide
  rw [hn] at hk
  rcases (by omega : (0 ≤ k ∧ k < 10) ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 55)) with h | h | h | h | h | h
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 0 10 k194_5_6_0 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 10 10 k194_5_6_10 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 20 10 k194_5_6_20 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 30 10 k194_5_6_30 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 40 10 k194_5_6_40 k h.1 (by omega)
  · exact rangeAll_sound (gRrun (colFibers CoreA2g.f0 194) (InDA2.TTsaaD 5 6 6) (posA (x2Mult 2 6) (194 - x2AOff 2 6)) (x2AOff 2 6) (x2SOff 2 5) (nS 2 5)) 50 5 k194_5_6_50 k h.1 (by omega)
theorem s194_5_7 : segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 5 7 = true := by decide +kernel
theorem col194_6 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 6 v) = true := by decide +kernel
theorem col194_7 : (List.finRange 8).all (fun v => segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 7 v) = true := by decide +kernel
theorem col194 : ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 194) 194 u v = true := by
  intro u v
  fin_cases u
  · exact List.all_eq_true.mp col194_0 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col194_1 v (List.mem_finRange v)
  · fin_cases v
    · exact s194_2_0
    · exact s194_2_1
    · exact s194_2_2
    · exact s194_2_3
    · exact s194_2_4
    · exact s194_2_5
    · exact s194_2_6
    · exact s194_2_7
  · fin_cases v
    · exact s194_3_0
    · exact s194_3_1
    · exact s194_3_2
    · exact s194_3_3
    · exact s194_3_4
    · exact s194_3_5
    · exact s194_3_6
    · exact s194_3_7
  · fin_cases v
    · exact s194_4_0
    · exact s194_4_1
    · exact s194_4_2
    · exact s194_4_3
    · exact s194_4_4
    · exact s194_4_5
    · exact s194_4_6
    · exact s194_4_7
  · fin_cases v
    · exact s194_5_0
    · exact s194_5_1
    · exact s194_5_2
    · exact s194_5_3
    · exact s194_5_4
    · exact s194_5_5
    · exact s194_5_6
    · exact s194_5_7
  · exact List.all_eq_true.mp col194_6 v (List.mem_finRange v)
  · exact List.all_eq_true.mp col194_7 v (List.mem_finRange v)

end ThreeCopyQutritWerner.X2.InFA2
